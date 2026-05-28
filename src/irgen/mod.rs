//! # Homework: IR Generation
//!
//! The goal of this homework is to translate the components of a C file into KECC IR. While doing
//! so, you will familarize yourself with the structure of KECC IR, and understand the semantics of
//! C in terms of KECC.
//!
//! We highly recommend checking out the [slides][slides] and [github repo][github-qna-irgen] for
//! useful information.
//!
//! ## Guide
//!
//! ### High Level Guide
//!
//! Please watch the following video from 2020 along the lecture slides.
//! - [Intermediate Representation][ir]
//! - [IRgen (Overview)][irgen-overview]
//!
//! ### Coding Guide
//!
//! We highly recommend you copy-and-paste the code given in the following lecture videos from 2020:
//! - [IRgen (Code, Variable Declaration)][irgen-var-decl]
//! - [IRgen (Code, Function Definition)][irgen-func-def]
//! - [IRgen (Code, Statement 1)][irgen-stmt-1]
//! - [IRgen (Code, Statement 2)][irgen-stmt-2]
//!
//! The skeleton code roughly consists of the code for the first two videos, but you should still
//! watch them to have an idea of what the code is like.
//!
//! [slides]: https://docs.google.com/presentation/d/1SqtU-Cn60Sd1jkbO0OSsRYKPMIkul0eZoYG9KpMugFE/edit?usp=sharing
//! [ir]: https://youtu.be/7CY_lX5ZroI
//! [irgen-overview]: https://youtu.be/YPtnXlKDSYo
//! [irgen-var-decl]: https://youtu.be/HjARCUoK08s
//! [irgen-func-def]: https://youtu.be/Rszt9x0Xu_0
//! [irgen-stmt-1]: https://youtu.be/jFahkyxm994
//! [irgen-stmt-2]: https://youtu.be/UkaXaNw462U
//! [github-qna-irgen]: https://github.com/kaist-cp/cs420/labels/homework%20-%20irgen
use core::cmp::Ordering;
use core::convert::TryFrom;
use core::{fmt, mem};
use std::collections::{BTreeMap, HashMap};
use std::ops::Deref;

use itertools::izip;
use lang_c::ast::*;
use lang_c::driver::Parse;
use lang_c::span::Node;
use thiserror::Error;

use crate::ir::{DtypeError, HasDtype, Named};
use crate::write_base::WriteString;
use crate::*;

#[derive(Debug)]
pub struct IrgenError {
    pub code: String,
    pub message: IrgenErrorMessage,
}

impl IrgenError {
    pub fn new(code: String, message: IrgenErrorMessage) -> Self {
        Self { code, message }
    }
}

impl fmt::Display for IrgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\r\n\r\ncode: {}", self.message, self.code)
    }
}

/// Error format when a compiler error happens.
///
/// Feel free to add more kinds of errors.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum IrgenErrorMessage {
    /// For uncommon error
    #[error("{message}")]
    Misc { message: String },
    #[error("called object `{callee:?}` is not a function or function pointer")]
    NeedFunctionOrFunctionPointer { callee: ir::Operand },
    #[error("redefinition, `{name}`")]
    Redefinition { name: String },
    #[error("`{dtype}` conflicts prototype's dtype, `{protorype_dtype}`")]
    ConflictingDtype {
        dtype: ir::Dtype,
        protorype_dtype: ir::Dtype,
    },
    #[error("{dtype_error}")]
    InvalidDtype { dtype_error: DtypeError },
    #[error("l-value required as {message}")]
    RequireLvalue { message: String },
}

/// A C file going through IR generation.
#[derive(Default, Debug)]
pub struct Irgen {
    /// Declarations made in the C file (e.g, global variables and functions)
    decls: BTreeMap<String, ir::Declaration>,
    /// Type definitions made in the C file (e.g, typedef my_type = int;)
    typedefs: HashMap<String, ir::Dtype>,
    /// Structs defined in the C file,
    // TODO: explain how to use this.
    structs: HashMap<String, Option<ir::Dtype>>,
    /// Temporary counter for anonymous structs. One should not need to use this any more.
    struct_tempid_counter: usize,
}

impl Translate<Parse> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &Parse) -> Result<Self::Target, Self::Error> {
        self.translate(&source.unit)
    }
}

impl Translate<TranslationUnit> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &TranslationUnit) -> Result<Self::Target, Self::Error> {
        for ext_decl in &source.0 {
            match &ext_decl.node {
                ExternalDeclaration::Declaration(var) => {
                    self.add_declaration(&var.node)?;
                }
                ExternalDeclaration::StaticAssert(_) => {
                    panic!("ExternalDeclaration::StaticAssert is unsupported")
                }
                ExternalDeclaration::FunctionDefinition(func) => {
                    self.add_function_definition(&func.node)?;
                }
            }
        }

        let decls = mem::take(&mut self.decls);
        let structs = mem::take(&mut self.structs);
        Ok(Self::Target { decls, structs })
    }
}

impl Irgen {
    const BID_INIT: ir::BlockId = ir::BlockId(0);
    // `0` is used to create `BID_INIT`
    const BID_COUNTER_INIT: usize = 1;
    const TEMPID_COUNTER_INIT: usize = 0;

    /// Add a declaration. It can be either a struct, typedef, or a variable.
    fn add_declaration(&mut self, source: &Declaration) -> Result<(), IrgenError> {
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&source.specifiers).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
        let base_dtype = base_dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("{source:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        let base_dtype = if let ir::Dtype::Struct { name, fields, .. } = &base_dtype {
            if let Some(name) = name {
                let _ = self.structs.entry(name.to_string()).or_insert(None);
            }

            if fields.is_some() {
                base_dtype
                    .resolve_structs(&mut self.structs, &mut self.struct_tempid_counter)
                    .map_err(|e| {
                        IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::InvalidDtype { dtype_error: e },
                        )
                    })?
            } else {
                base_dtype
            }
        } else {
            base_dtype
        };

        for init_decl in &source.declarators {
            let declarator = &init_decl.node.declarator.node;
            let name = name_of_declarator(declarator);
            // reference cloning based dtype in translate_decl
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| {
                    IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::InvalidDtype { dtype_error: e },
                    )
                })?
                .deref()
                .clone();
            let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
            if !is_typedef && is_invalid_structure(&dtype, &self.structs) {
                return Err(IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::Misc {
                        message: "incomplete struct type".to_string(),
                    },
                ));
            }

            if is_typedef {
                // Add new typedef if nothing has been declared before
                let prev_dtype = self
                    .typedefs
                    .entry(name.clone())
                    .or_insert_with(|| dtype.clone());

                if prev_dtype != &dtype {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::ConflictingDtype {
                            dtype,
                            protorype_dtype: prev_dtype.clone(),
                        },
                    ));
                }

                continue;
            }

            // Creates a new declaration based on the dtype.
            let mut decl = ir::Declaration::try_from(dtype.clone()).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;

            // If `initializer` exists, convert initializer to a constant value
            if let Some(initializer) = init_decl.node.initializer.as_ref() {
                if !is_valid_initializer(&initializer.node, &dtype, &self.structs) {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::Misc {
                            message: "initializer is not valid".to_string(),
                        },
                    ));
                }

                match &mut decl {
                    ir::Declaration::Variable {
                        initializer: var_initializer,
                        ..
                    } => {
                        if var_initializer.is_some() {
                            return Err(IrgenError::new(
                                format!("{source:#?}"),
                                IrgenErrorMessage::Redefinition { name },
                            ));
                        }
                        *var_initializer = Some(initializer.node.clone());
                    }
                    ir::Declaration::Function { .. } => {
                        return Err(IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::Misc {
                                message: "illegal initializer (only variables can be initialized)"
                                    .to_string(),
                            },
                        ));
                    }
                }
            }

            self.add_decl(&name, decl)?;
        }

        Ok(())
    }

    /// Add a function definition.
    fn add_function_definition(&mut self, source: &FunctionDefinition) -> Result<(), IrgenError> {
        // Creates name and signature.
        let specifiers = &source.specifiers;
        let declarator = &source.declarator.node;

        let name = name_of_declarator(declarator);
        let name_of_params = name_of_params_from_function_declarator(declarator)
            .expect("declarator is not from function definition");

        // finding out the type from the specifiers.
        let (base_dtype, is_typedef) = ir::Dtype::try_from_ast_declaration_specifiers(specifiers)
            .map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        // typedef cant be function definition
        if is_typedef {
            return Err(IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::Misc {
                    message: "function definition declared typedef".into(),
                },
            ));
        }

        // the declarator also have a say in type like
        // int x; -> x is an int
        // int *x; -> x is a pointer to int
        // int x[10] -> x is an array with 10 int
        // for this it is a dtype of the function so it should look a bit different but whatever
        // lol
        //
        let dtype = base_dtype
            .with_ast_declarator(declarator)
            .map_err(|e| {
                IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?
            .deref()
            .clone();
        let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        // this dtype should always be a function type but with different returns and params types
        let signature = ir::FunctionSignature::new(dtype.clone());

        // Adds new declaration if nothing has been declared before
        let decl = ir::Declaration::try_from(dtype).unwrap();
        self.add_decl(&name, decl)?;

        // int fibonacci(int x) {
        //   ..
        //   in case of recursion, we have to add decl here instead of the end of the translation
        //   return fibonacci (x - 1) + fibonacci (x-2)
        // }

        // Prepare scope for global variable
        let global_scope: HashMap<_, _> = self
            .decls
            .iter()
            .map(|(name, decl)| {
                let dtype = decl.dtype();
                let pointer = ir::Constant::global_variable(name.clone(), dtype);
                let operand = ir::Operand::constant(pointer);
                (name.clone(), operand)
            })
            .collect();

        // Prepares for irgen pass.
        let mut irgen = IrgenFunc {
            return_type: signature.ret.clone(),
            bid_init: Irgen::BID_INIT,
            phinodes_init: Vec::new(),
            allocations: Vec::new(),
            blocks: BTreeMap::new(),
            bid_counter: Irgen::BID_COUNTER_INIT,
            tempid_counter: Irgen::TEMPID_COUNTER_INIT,
            typedefs: &self.typedefs,
            structs: &self.structs,
            // Initial symbol table has scope for global variable already
            symbol_table: vec![global_scope],
        };
        let mut context = Context::new(irgen.bid_init);

        // Enter variable scope for alloc registers matched with function parameters
        irgen.enter_scope();

        // Creates the init block that stores arguments.
        irgen
            .translate_parameter_decl(&signature, irgen.bid_init, &name_of_params, &mut context)
            .map_err(|e| {
                IrgenError::new(format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"), e)
            })?;

        // Translates statement.
        irgen.translate_stmt(&source.statement.node, &mut context, None, None)?;

        // Creates the end block
        let ret = signature.ret.set_const(false);
        let value = if ret == ir::Dtype::unit() {
            ir::Operand::constant(ir::Constant::unit())
        } else if ret == ir::Dtype::INT {
            // If "main" function, default return value is `0` when return type is `int`
            if name == "main" {
                ir::Operand::constant(ir::Constant::int(0, ret))
            } else {
                ir::Operand::constant(ir::Constant::undef(ret))
            }
        } else {
            ir::Operand::constant(ir::Constant::undef(ret))
        };

        // Last Block of the function
        irgen.insert_block(context, ir::BlockExit::Return { value });

        // Exit variable scope created above
        irgen.exit_scope();

        let func_def = ir::FunctionDefinition {
            allocations: irgen.allocations,
            blocks: irgen.blocks,
            bid_init: irgen.bid_init,
        };

        let decl = self
            .decls
            .get_mut(&name)
            .unwrap_or_else(|| panic!("The declaration of `{name}` must exist"));
        if let ir::Declaration::Function { definition, .. } = decl {
            if definition.is_some() {
                return Err(IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::Misc {
                        message: format!("the name `{name}` is defined multiple time"),
                    },
                ));
            }

            // Update function definition
            *definition = Some(func_def);
        } else {
            panic!("`{name}` must be function declaration")
        }

        Ok(())
    }

    /// Adds a possibly existing declaration.
    ///
    /// Returns error if the previous declearation is incompatible with `decl`.
    fn add_decl(&mut self, name: &str, decl: ir::Declaration) -> Result<(), IrgenError> {
        let Some(old_decl) = self.decls.insert(name.to_string(), decl.clone()) else {
            return Ok(());
        };

        // Check if type is conflicting for pre-declared one
        if !old_decl.is_compatible(&decl) {
            return Err(IrgenError::new(
                name.to_string(),
                IrgenErrorMessage::ConflictingDtype {
                    dtype: old_decl.dtype(),
                    protorype_dtype: decl.dtype(),
                },
            ));
        }

        Ok(())
    }
}

/// Storage for instructions up to the insertion of a block
#[derive(Debug)]
struct Context {
    /// The block id of the current context.
    bid: ir::BlockId,
    /// Current instructions of the block.
    instrs: Vec<Named<ir::Instruction>>,
}

impl Context {
    /// Create a new context with block number bid
    fn new(bid: ir::BlockId) -> Self {
        Self {
            bid,
            instrs: Vec::new(),
        }
    }

    // Adds `instr` to the current context.
    fn insert_instruction(
        &mut self,
        instr: ir::Instruction,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let dtype = instr.dtype();
        self.instrs.push(Named::new(None, instr));

        Ok(ir::Operand::register(
            ir::RegisterId::temp(self.bid, self.instrs.len() - 1),
            dtype,
        ))
    }
}

/// A C function being translated.
struct IrgenFunc<'i> {
    /// return type of the function.
    return_type: ir::Dtype,
    /// initial block id for the function, typically 0.
    bid_init: ir::BlockId,
    /// arguments represented as initial phinodes. Order must be the same of that given in the C
    /// function.
    phinodes_init: Vec<Named<ir::Dtype>>,
    /// local allocations.
    allocations: Vec<Named<ir::Dtype>>,
    /// Map from block id to basic blocks
    blocks: BTreeMap<ir::BlockId, ir::Block>,
    /// current block id. `blocks` must have an entry for all ids less then this
    bid_counter: usize,
    /// current temporary id. Used to create temporary names in the IR for e.g,
    tempid_counter: usize,
    /// Usable definitions
    typedefs: &'i HashMap<String, ir::Dtype>,
    /// Usable structs
    // TODO: Add examples on how to use properly use this field.
    structs: &'i HashMap<String, Option<ir::Dtype>>,
    /// Current symbol table. The initial symbol table has the global variables.
    symbol_table: Vec<HashMap<String, ir::Operand>>,
}

impl IrgenFunc<'_> {
    /// Allocate a new block id.
    fn alloc_bid(&mut self) -> ir::BlockId {
        let bid = self.bid_counter;
        self.bid_counter += 1;
        ir::BlockId(bid)
    }

    /// Allocate a new temporary id.
    fn alloc_tempid(&mut self) -> String {
        let tempid = self.tempid_counter;
        self.tempid_counter += 1;
        format!("t{tempid}")
    }

    /// Create a new allocation with type given by `alloc`.
    fn insert_alloc(&mut self, alloc: Named<ir::Dtype>) -> ir::RegisterId {
        self.allocations.push(alloc);
        let id = self.allocations.len() - 1;
        ir::RegisterId::local(id)
    }

    /// Insert a new block `context` with exit instruction `exit`.
    ///
    /// # Panic
    ///
    /// Panics if another block with the same bid as `context` already existed.
    fn insert_block(&mut self, context: Context, exit: ir::BlockExit) {
        let block = ir::Block {
            phinodes: if context.bid == self.bid_init {
                self.phinodes_init.clone()
            } else {
                Vec::new()
            },
            instructions: context.instrs,
            exit,
        };
        if self.blocks.insert(context.bid, block).is_some() {
            panic!("the bid `{}` is defined multiple time", context.bid)
        }
    }

    /// Enter a scope and create a new symbol table entry, i.e, we are at a `{` in the function.
    fn enter_scope(&mut self) {
        self.symbol_table.push(HashMap::new());
    }

    /// Exit a scope and remove the a oldest symbol table entry. i.e, we are at a `}` in the
    /// function.
    ///
    /// # Panic
    ///
    /// Panics if there are no scopes to exit, i.e, the function has a unmatched `}`.
    fn exit_scope(&mut self) {
        let _unused = self.symbol_table.pop().unwrap();
        debug_assert!(!self.symbol_table.is_empty())
    }

    /// Inserts `var` with `value` to the current symbol table.
    ///
    /// Returns Ok() if the current scope has no previously-stored entry for a given variable.
    fn insert_symbol_table_entry(
        &mut self,
        var: String,
        value: ir::Operand,
    ) -> Result<(), IrgenErrorMessage> {
        let cur_scope = self
            .symbol_table
            .last_mut()
            .expect("symbol table has no valid scope");
        if cur_scope.insert(var.clone(), value).is_some() {
            return Err(IrgenErrorMessage::Redefinition { name: var });
        }

        Ok(())
    }

    /// [SELF]
    ///  Get the allocation to the variable with name var
    fn lookup_symbol_table_entry(
        &mut self,
        var: &String,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let mut operand = None;

        for scope in self.symbol_table.iter().rev() {
            operand = scope.get(var).clone();
            if let Some(val) = operand {
                return Ok(val.clone());
            }
        }

        Err(IrgenErrorMessage::Misc {
            message: format!("can't find {var} in scope"),
        })
    }

    /// Transalte a C statement `stmt` under the current block `context`, with `continue` block
    /// `bid_continue` and break block `bid_break`.
    fn translate_stmt(
        &mut self,
        stmt: &Statement,
        context: &mut Context,
        bid_continue: Option<ir::BlockId>,
        bid_break: Option<ir::BlockId>,
    ) -> Result<(), IrgenError> {
        match stmt {
            Statement::Labeled(_) => panic!("labelled outside switch? bad!"),
            Statement::Compound(items) => {
                self.enter_scope();

                for item in items {
                    match &item.node {
                        BlockItem::Declaration(decl) => self
                            .translate_decl(&decl.node, context)
                            .map_err(|e| IrgenError::new(decl.write_string(), e))?,
                        BlockItem::Statement(stmt) => {
                            self.translate_stmt(&stmt.node, context, bid_continue, bid_break)?
                        }
                        BlockItem::StaticAssert(_) => {
                            panic!("BlockItem::StaticAssert is not supported")
                        }
                    }
                }

                Ok(())
            }
            // like
            // x+1;
            //
            // we still have to eval the expr but we dont have to store the value anywhere
            Statement::Expression(expr) => {
                if let Some(expr) = expr {
                    let _unused = self
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError::new(expr.write_string(), e))?;
                }

                Ok(())
            }
            Statement::If(stmt) => {
                let bid_then = self.alloc_bid();
                let bid_else = self.alloc_bid();
                let bid_end = self.alloc_bid();

                // translating condition with all the bid of then and else with new context with
                // bid_end (because you have to jump to bid_end if cant jump to else or then)
                // commiting last block
                //
                // ok, i understand now. so this is the last instruction of the previous block. we
                // are gonna jump conditionally based on the condition. then, after inserting the
                // conditional jump as the last exit of the block, we commit the previous block and
                // replace the context of the caller with the bid_end of this if statement (which
                // has empty instruction)
                self.translate_condition(
                    &stmt.node.condition.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_then,
                    bid_else,
                )
                .map_err(|e| IrgenError::new(stmt.node.condition.write_string(), e))?;

                // make new context for the then block
                let mut context_then = Context::new(bid_then);

                // translate the then stmt and put all the translated inside the context
                self.translate_stmt(
                    &stmt.node.then_statement.node,
                    &mut context_then,
                    bid_continue,
                    bid_break,
                )?;

                // commit the then block with jump arg being the next block we're translating
                self.insert_block(
                    context_then,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                let mut context_else = Context::new(bid_else);
                if let Some(else_block) = &stmt.node.else_statement {
                    self.translate_stmt(&else_block.node, context, bid_continue, bid_break)?;
                }

                self.insert_block(
                    context_else,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );
                Ok(())
            }
            Statement::Switch(stmt) => {
                let switch_stmt = &stmt.node;

                let value = self
                    .translate_expr_rvalue(&switch_stmt.expression.node, context)
                    .map_err(|e| IrgenError::new(switch_stmt.expression.write_string(), e))?;

                let bid_end = self.alloc_bid();
                let (cases, bid_default) =
                    self.translate_switch_body(&switch_stmt.statement.node, bid_end)?;

                self.insert_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::Switch {
                        value,
                        default: ir::JumpArg::new(bid_default, Vec::new()),
                        cases,
                    },
                );

                Ok(())
            }
            Statement::While(stmt) => {
                let while_stmt = &stmt.node;

                let bid_cond = self.alloc_bid();

                // committing the previous block and jumping to the condition block
                // now context = bid_cond
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                let bid_body = self.alloc_bid();
                let bid_end = self.alloc_bid();

                // translating the condition block and committing it
                // now context = bid_end
                self.translate_condition(
                    &while_stmt.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(while_stmt.expression.write_string(), e))?;

                self.enter_scope();

                let mut context_body = Context::new(bid_body);

                self.translate_stmt(
                    &while_stmt.statement.node,
                    &mut context_body,
                    Some(bid_cond),
                    Some(bid_end),
                )?;

                self.insert_block(
                    context_body,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                self.exit_scope();

                Ok(())
            }
            Statement::DoWhile(stmt) => {
                // do -> condition -> do -> ... -> end
                let dowhile_stmt = &stmt.node;

                let bid_body = self.alloc_bid();

                // commit the block before
                // now context is bid_body
                self.insert_block(
                    mem::replace(context, Context::new(bid_body)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_body, Vec::new()),
                    },
                );

                self.enter_scope();

                let bid_cond = self.alloc_bid();
                let bid_end = self.alloc_bid();

                // do while do anything without condition first
                self.translate_stmt(
                    &dowhile_stmt.statement.node,
                    context,
                    Some(bid_cond),
                    Some(bid_end),
                )?;

                self.exit_scope();

                // commit body block
                // now context = bid_cond
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                // commit condition block
                // now context = bid_end
                self.translate_condition(
                    &dowhile_stmt.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(dowhile_stmt.expression.write_string(), e))?;

                Ok(())
            }
            Statement::For(stmt) => {
                // sanity check
                // init -> condition -> body -> step -> condition ... -> end
                // 5 new blocks
                // init, condition, body, step, end
                let for_stmt = &stmt.node;

                // commit the current context and the exit instruction of the current context is to
                // jump to this new block for initializer
                let bid_init = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_init)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_init, Vec::new()),
                    },
                );

                self.enter_scope();

                self.translate_for_initializer(&for_stmt.initializer.node, context)
                    .map_err(|e| IrgenError::new(for_stmt.initializer.write_string(), e))?;

                let bid_cond = self.alloc_bid(); // for the conditional block
                // committing the init block and jump to the conditional block
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                let bid_body = self.alloc_bid();
                let bid_step = self.alloc_bid();
                let bid_end = self.alloc_bid();

                self.translate_opt_condition(
                    &for_stmt.condition,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(for_stmt.condition.write_string(), e))?;

                self.enter_scope(); //entering scope for the body of the execution

                let mut context_body = Context::new(bid_body);
                self.translate_stmt(
                    &for_stmt.statement.node,
                    &mut context_body,
                    Some(bid_step),
                    Some(bid_end),
                )?;

                self.exit_scope();

                self.insert_block(
                    context_body,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_step, Vec::new()),
                    },
                );

                let mut context_step = Context::new(bid_step);

                if let Some(step_expr) = &for_stmt.step {
                    let _unused = self
                        .translate_expr_rvalue(&step_expr.node, &mut context_step)
                        .map_err(|e| IrgenError::new(step_expr.write_string(), e))?;
                }

                self.insert_block(
                    context_step,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                // exit the scope from the init
                self.exit_scope();

                Ok(())
            }
            Statement::Goto(node) => todo!(),
            Statement::Continue => {
                // if there is a continue then there should be a continuation block
                let bid_cont = bid_continue.ok_or_else(|| {
                    IrgenError::new(
                        "continuation not found".to_string(),
                        IrgenErrorMessage::Misc {
                            message: "can't find continuation of this block".to_string(),
                        },
                    )
                })?;

                // allocate next block
                let mut next_context = self.alloc_bid();

                self.insert_block(
                    mem::replace(context, Context::new(next_context)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cont, Vec::new()),
                    },
                );

                Ok(())
            }
            Statement::Break => {
                let bid_break = bid_break.ok_or_else(|| {
                    IrgenError::new(
                        "continuation not found".to_string(),
                        IrgenErrorMessage::Misc {
                            message: "can't find continuation of this block after break"
                                .to_string(),
                        },
                    )
                })?;

                // allocate next block
                let mut next_context = self.alloc_bid();

                self.insert_block(
                    mem::replace(context, Context::new(next_context)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_break, Vec::new()),
                    },
                );

                Ok(())
            }
            Statement::Return(val) => {
                // not sure if this bid is correct.
                // might need to jump to bid_continue? have to check when doing function call
                //
                // [UPDATE] apparently there is a block exit called return and you can return a
                // value there. I guess if there is no value then i just return unit type.
                let bid_next = self.alloc_bid();
                let value = if let Some(ret_val) = &val {
                    self.translate_expr_rvalue(&ret_val.node, context)
                        .map_err(|e| IrgenError::new(ret_val.write_string(), e))?
                } else {
                    ir::Operand::Constant(ir::Constant::unit())
                };

                // implicit type cast
                let value = self
                    .translate_typecast(value, &self.return_type.clone(), context)
                    .map_err(|e| IrgenError::new(val.write_string(), e))?;

                self.insert_block(
                    mem::replace(context, Context::new(bid_next)),
                    ir::BlockExit::Return { value },
                );
                Ok(())
            }
            _ => panic!("statement not supported"),
        }
    }

    fn translate_switch_body(
        &mut self,
        statement: &Statement,
        bid_end: ir::BlockId,
    ) -> Result<(Vec<(ir::Constant, ir::JumpArg)>, ir::BlockId), IrgenError> {
        let stmts = if let Statement::Compound(stmts) = statement {
            stmts
        } else {
            panic!("only compound statement in switch statement")
        };

        let mut cases: Vec<(ir::Constant, ir::JumpArg)> = Vec::new();
        let mut default: Option<ir::BlockId> = None;

        self.enter_scope();

        for stmt in stmts {
            match &stmt.node {
                BlockItem::Statement(labelled_stmt) => self.translate_switch_body_inner(
                    &labelled_stmt.node,
                    &mut cases,
                    &mut default,
                    bid_end,
                )?,
                _ => panic!("statement in switch can only be labelled statement"),
            }
        }

        self.exit_scope();

        // if there is no default block just skip to the end
        let default = default.unwrap_or(bid_end);

        Ok((cases, default))
    }

    fn translate_switch_body_inner(
        &mut self,
        statement: &Statement,
        cases: &mut Vec<(ir::Constant, ir::JumpArg)>,
        default: &mut Option<ir::BlockId>,
        bid_end: ir::BlockId,
    ) -> Result<(), IrgenError> {
        // stmt => case 1: {A1; break;}
        //
        let bid_body = self.alloc_bid();
        let mut context_body = Context::new(bid_body);
        let label_stmt = if let Statement::Labeled(label) = statement {
            &label.node
        } else {
            panic!("statement inside the switch body should all be labeled statement");
        };

        // translating the case body and getting it case value
        let case = self.translate_switch_body_label_statement(label_stmt, bid_body, bid_end)?;

        if let Some(case) = case {
            if !case.is_integer_constant() {
                return Err(IrgenError::new(
                    case.to_string(),
                    IrgenErrorMessage::Misc {
                        message: "case expression should resolve into an integer constant"
                            .to_string(),
                    },
                ));
            }

            // TODO: consider the case that it has the same value but different width
            // [HERE] my solution attempt. i just have faith that it will unwrap
            if cases
                .iter()
                .any(|(c, _)| case.get_int().unwrap().0 == c.get_int().unwrap().0)
            {
                return Err(IrgenError::new(
                    label_stmt.write_string(),
                    IrgenErrorMessage::Misc {
                        message: "duplicate label case".to_string(),
                    },
                ));
            }
            cases.push((case, ir::JumpArg::new(bid_body, Vec::new())));
        } else {
            if default.is_some() {
                return Err(IrgenError::new(
                    label_stmt.write_string(),
                    IrgenErrorMessage::Misc {
                        message: "duplicate default cases".to_string(),
                    },
                ));
            }
            *default = Some(bid_body);
        }

        Ok(())
    }

    fn translate_switch_body_label_statement(
        &mut self,
        label_stmt: &LabeledStatement,
        bid_curr: ir::BlockId,
        bid_end: ir::BlockId,
    ) -> Result<Option<ir::Constant>, IrgenError> {
        let case: Option<ir::Constant> = match &label_stmt.label.node {
            Label::Case(expr) => {
                let con = ir::Constant::try_from(&expr.node).map_err(|_| {
                    IrgenError::new(
                        expr.write_string(),
                        IrgenErrorMessage::Misc {
                            message: "only allow constant as case label".to_string(),
                        },
                    )
                })?;
                Some(con)
            }
            Label::Default => None,
            _ => panic!("Label::Identifier and Label::Range is not supported in this KECC"),
        };

        // cause we expect like { A1; break; } so it has to be a compound
        let items = if let Statement::Compound(items) = &label_stmt.statement.node {
            items
        } else {
            panic!("statement label is not a compound statement");
        };

        self.enter_scope();

        let (last, items) = items
            .split_last()
            .expect("should have break; as the last item");

        let mut context_body = Context::new(bid_curr);

        for item in items {
            match &item.node {
                BlockItem::Declaration(decl) => {
                    self.translate_decl(&decl.node, &mut context_body)
                        .map_err(|e| IrgenError::new(decl.write_string(), e))?;
                }
                BlockItem::Statement(stmt) => {
                    self.translate_stmt(&stmt.node, &mut context_body, None, None)?;
                }
                BlockItem::StaticAssert(_) => panic!("not supported"),
            }
        }

        let last_stmt = if let BlockItem::Statement(stmt) = &last.node {
            stmt.node.clone()
        } else {
            panic!("last item HAVE TO be a break. which is a statement")
        };

        assert_eq!(last_stmt, Statement::Break);

        // conclude the block to the ending block (we made sure that the last statement is break
        // anyway)
        self.insert_block(
            context_body,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        self.exit_scope();

        Ok(case)
    }

    fn translate_opt_condition(
        &mut self,
        cond: &Option<Box<Node<Expression>>>,
        context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        if let Some(condition) = cond {
            self.translate_condition(&condition.node, context, bid_then, bid_else)
        } else {
            self.insert_block(
                context,
                ir::BlockExit::Jump {
                    arg: ir::JumpArg::new(bid_then, Vec::new()),
                },
            );
            Ok(())
        }
    }

    fn translate_for_initializer(
        &mut self,
        init: &ForInitializer,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        let _unused = match init {
            ForInitializer::Empty => (),
            ForInitializer::Expression(expr) => {
                let _unused = self.translate_expr_rvalue(&expr.node, context)?;
            }
            ForInitializer::Declaration(decl) => {
                return self.translate_decl(&decl.node, context);
            }
            ForInitializer::StaticAssert(node) => panic!("not supported"),
        };
        Ok(())
    }

    fn translate_condition(
        &mut self,
        cond: &Expression,
        mut context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        let condition = self.translate_expr_rvalue(cond, &mut context)?;
        let condition = self.translate_typecast_to_bool(condition, &mut context)?;

        self.insert_block(
            context,
            ir::BlockExit::ConditionalJump {
                condition,
                arg_then: ir::JumpArg::new(bid_then, Vec::new()),
                arg_else: ir::JumpArg::new(bid_else, Vec::new()),
            },
        );

        Ok(())
    }

    fn translate_typecast_to_bool(
        &mut self,
        value: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        self.translate_typecast(value, &ir::Dtype::BOOL, context)
    }

    fn translate_decl(
        &mut self,
        decl: &Declaration,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        // int x*
        // int => specifiers
        // x => declarator
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&decl.specifiers)
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

        // declaration can't be typedef
        assert!(!is_typedef);

        for init_decl in &decl.declarators {
            let declarator = &init_decl.node.declarator.node;
            // see reference in fn add_declaration on how to clone and deref
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?
                .deref()
                .clone();
            let dtype = dtype
                .resolve_typedefs(&self.typedefs)
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
            let name = name_of_declarator(declarator);

            match dtype {
                ir::Dtype::Unit { is_const } => {
                    return Err(IrgenErrorMessage::InvalidDtype {
                        dtype_error: DtypeError::Misc {
                            message: "can't declare thing with type `void`".to_string(),
                        },
                    });
                }
                ir::Dtype::Int { .. }
                | ir::Dtype::Float { .. }
                | ir::Dtype::Pointer { .. }
                | ir::Dtype::Array { .. }
                | ir::Dtype::Struct { .. } => {
                    let init_value = if let Some(value) = &init_decl.node.initializer {
                        Some(self.translate_initializer(&value.node, context)?)
                    } else {
                        None
                    };

                    let _unused = self.translate_alloc(&name, &dtype, init_value, context)?;
                }
                ir::Dtype::Function { ret, params } => todo!(),
                ir::Dtype::Typedef { name, is_const } => {
                    panic!("typedefs should be resolved by now")
                }
            }
        }

        Ok(())
    }

    fn translate_initializer(
        &mut self,
        initializer: &Initializer,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match initializer {
            Initializer::Expression(expr) => self.translate_expr_rvalue(&expr.node, context),
            Initializer::List(_) => panic!("Initializer::List is not supported"),
        }
    }

    fn translate_func_call(
        &mut self,
        call: &CallExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let callee = self.translate_expr_rvalue(&call.callee.node, context)?;
        let function_pointer = callee.dtype();
        let inner = function_pointer.get_pointer_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer {
                callee: callee.clone(),
            }
        })?;
        let (return_type, param_type) = inner.get_function_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer {
                callee: callee.clone(),
            }
        })?;

        let args = call
            .arguments
            .iter()
            .map(|a| self.translate_expr_rvalue(&a.node, context))
            .collect::<Result<Vec<_>, _>>()?;

        if args.len() != param_type.len() {
            return Err(IrgenErrorMessage::Misc {
                message: "length of argument doesn't match the length of parameter".to_string(),
            });
        }

        // typecast all the args to be the correct type for the function param
        let args = izip!(args, param_type)
            .map(|(arg, ptype)| self.translate_typecast(arg, ptype, context))
            .collect::<Result<Vec<_>, _>>()?;

        context.insert_instruction(ir::Instruction::Call {
            callee,
            args,
            return_type: return_type.clone().set_const(false),
        })
    }

    fn translate_conditional(
        &mut self,
        cond_expr: &ConditionalExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let bid_then = self.alloc_bid();
        let bid_else = self.alloc_bid();
        let bid_end = self.alloc_bid();

        // to create the new condition translation, we have to commit the previous block entirely
        let condition = self.translate_condition(
            &cond_expr.condition.node,
            mem::replace(context, Context::new(bid_end)),
            bid_then,
            bid_else,
        )?;

        let mut context_then = Context::new(bid_then);
        let mut context_else = Context::new(bid_else);

        let val_then =
            self.translate_expr_rvalue(&cond_expr.then_expression.node, &mut context_then)?;
        let val_else =
            self.translate_expr_rvalue(&cond_expr.else_expression.node, &mut context_else)?;

        let merged_dtype = self.merge_dtype(&val_then.dtype(), &val_else.dtype())?;

        let val_then = self.translate_typecast(val_then, &merged_dtype, &mut context_then)?;
        let val_else = self.translate_typecast(val_else, &merged_dtype, &mut context_else)?;

        // allocates at the stack
        //
        // the idea is that
        // conditional-jump c then_branch else_branch
        //
        // %t
        //
        // then_branch:
        // store val_then %t
        // j end
        //
        // else_branch:
        // store val_else %t
        // j end
        //
        // end:
        // load %t
        let temp_var = self.alloc_tempid();
        let ptr = self.alloc_ptr(&temp_var, &merged_dtype)?;

        // store at then
        let _unused = context_then.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: val_then,
        })?;

        // conclude then
        self.insert_block(
            context_then,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        // store at else
        let _unused = context_else.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: val_else,
        })?;

        // conclude else
        self.insert_block(
            context_else,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        // load at the end
        context.insert_instruction(ir::Instruction::Load { ptr })
    }

    // [SELF] have to check
    fn merge_dtype(
        &self,
        lhs_dtype: &ir::Dtype,
        rhs_dtype: &ir::Dtype,
    ) -> Result<ir::Dtype, IrgenErrorMessage> {
        //  should i resolve typedef??
        let lhs_dtype = lhs_dtype
            .clone()
            .resolve_typedefs(self.typedefs)
            .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
        let rhs_dtype = rhs_dtype
            .clone()
            .resolve_typedefs(self.typedefs)
            .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

        let merged_dtype = match (lhs_dtype.clone(), rhs_dtype.clone()) {
            (ir::Dtype::Unit { .. }, ir::Dtype::Unit { .. }) => todo!("can you merge a unit type?"),
            (
                ir::Dtype::Int {
                    width: lhs_width,
                    is_signed: lhs_is_signed,
                    is_const: lhs_is_const,
                },
                ir::Dtype::Int {
                    width: rhs_width,
                    is_signed: rhs_is_signed,
                    is_const: rhs_is_const,
                },
            ) => {
                let merged_width = lhs_width.max(rhs_width);
                assert_eq!(
                    lhs_is_signed, rhs_is_signed,
                    "{lhs_dtype} and {rhs_dtype} should have the same `is_signed`"
                );
                assert_eq!(
                    lhs_is_const, rhs_is_const,
                    "{lhs_dtype} and {rhs_dtype} should have the same `is_const`"
                );

                ir::Dtype::Int {
                    width: merged_width,
                    is_signed: lhs_is_signed,
                    is_const: lhs_is_const,
                }
            }
            (
                ir::Dtype::Float {
                    width: lhs_width,
                    is_const: lhs_is_const,
                },
                ir::Dtype::Float {
                    width: rhs_width,
                    is_const: rhs_is_const,
                },
            ) => {
                let merged_width = lhs_width.max(rhs_width);
                assert_eq!(
                    lhs_is_const, rhs_is_const,
                    "{lhs_dtype} and {rhs_dtype} should have the same `is_const`"
                );

                ir::Dtype::Float {
                    width: merged_width,
                    is_const: lhs_is_const,
                }
            }
            (
                ir::Dtype::Array {
                    inner: lhs_inner,
                    size: lhs_size,
                },
                ir::Dtype::Array {
                    inner: rhs_inner,
                    size: rhs_size,
                },
            ) => {
                assert_eq!(
                    lhs_size, rhs_size,
                    "array from both side should have equal size"
                );
                let merged_inner = self.merge_dtype(&lhs_inner, &rhs_inner)?;
                ir::Dtype::array(merged_inner, lhs_size)
            }
            (ir::Dtype::Struct { .. }, ir::Dtype::Struct { .. }) => {
                todo!("can struct be used like this?")
            }
            (ir::Dtype::Function { .. }, ir::Dtype::Function { .. }) => {
                todo!("can function be used like this?")
            }
            (ir::Dtype::Typedef { .. }, ir::Dtype::Typedef { .. }) => {
                panic!("typedef can't be assigned")
            }
            (_, _) => {
                return Err(IrgenErrorMessage::InvalidDtype {
                    dtype_error: DtypeError::Misc {
                        message: "both dtype should be the same to merge".to_string(),
                    },
                });
            }
        };

        Ok(merged_dtype)
    }

    fn translate_binary_operator_expression(
        &mut self,
        binop_expr: &BinaryOperatorExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let lhs_rvalue = self.translate_expr_rvalue(&binop_expr.lhs.node, context)?;
        let rhs_rvalue = self.translate_expr_rvalue(&binop_expr.rhs.node, context)?;

        //[SELF] this is array indexing might need to fix this later
        if binop_expr.operator.node.is_equiv(&BinaryOperator::Index) {
            let inner_dtype = lhs_rvalue
                .dtype()
                .get_array_inner()
                .ok_or_else(|| IrgenErrorMessage::InvalidDtype {
                    dtype_error: DtypeError::Misc {
                        message: "only array can use the index operator".to_string(),
                    },
                })?
                .clone();

            // its byte address so
            // index * 4 bytes (the size of i32)

            let offset: ir::Operand = context.insert_instruction(ir::Instruction::BinOp {
                op: BinaryOperator::Multiply,
                lhs: ir::Operand::constant(ir::Constant::int(4, ir::Dtype::INT)),
                rhs: rhs_rvalue,
                dtype: ir::Dtype::INT,
            })?;

            return context.insert_instruction(ir::Instruction::GetElementPtr {
                ptr: lhs_rvalue.clone(),
                offset: offset.clone(),
                dtype: inner_dtype.clone(),
            });
        }

        // [TODO] translate typecast according to the write up
        let dtype = self.resolve_type_binop(&lhs_rvalue.dtype(), &rhs_rvalue.dtype())?;

        let lhs_rvalue = self.translate_typecast(lhs_rvalue, &dtype, context)?;
        let rhs_rvalue = self.translate_typecast(rhs_rvalue, &dtype, context)?;

        match &binop_expr.operator.node {
            BinaryOperator::Index => panic!("why is index not resolved now???"),
            BinaryOperator::Multiply => todo!(),
            BinaryOperator::Divide => todo!(),
            BinaryOperator::Modulo => todo!(),
            BinaryOperator::Plus => todo!(),
            BinaryOperator::Minus => todo!(),
            BinaryOperator::ShiftLeft => todo!(),
            BinaryOperator::ShiftRight => todo!(),
            BinaryOperator::BitwiseAnd => todo!(),
            BinaryOperator::BitwiseXor => todo!(),
            BinaryOperator::BitwiseOr => todo!(),
            BinaryOperator::Less => todo!(),
            BinaryOperator::Greater => todo!(),
            BinaryOperator::LessOrEqual => todo!(),
            BinaryOperator::GreaterOrEqual => todo!(),
            BinaryOperator::Equals => todo!(),
            BinaryOperator::NotEquals => todo!(),
            BinaryOperator::LogicalAnd => todo!(),
            BinaryOperator::LogicalOr => todo!(),
            BinaryOperator::Assign => todo!(),
            BinaryOperator::AssignMultiply => todo!(),
            BinaryOperator::AssignDivide => todo!(),
            BinaryOperator::AssignModulo => todo!(),
            BinaryOperator::AssignPlus => todo!(),
            BinaryOperator::AssignMinus => todo!(),
            BinaryOperator::AssignShiftLeft => todo!(),
            BinaryOperator::AssignShiftRight => todo!(),
            BinaryOperator::AssignBitwiseAnd => todo!(),
            BinaryOperator::AssignBitwiseXor => todo!(),
            BinaryOperator::AssignBitwiseOr => todo!(),
        }
    }

    fn integer_promotions(
        &mut self,
        integer: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let integer_const = integer
            .get_constant()
            .ok_or_else(|| IrgenErrorMessage::Misc {
                message: "should be integer constant".to_string(),
            })?;

        match integer_const {
            ir::Constant::Int {
                value,
                width,
                is_signed,
            } => {
                let int_width = ir::Dtype::INT.get_int_width().unwrap();
                if width < &int_width {
                    return self.translate_typecast(integer, &ir::Dtype::INT, context);
                } else {
                    return Ok(integer);
                }
            }
            _ => panic!("only integer allowed"),
        }
    }

    fn resolve_type_binop(
        &self,
        lhs_dtype: &ir::Dtype,
        rhs_dtype: &ir::Dtype,
    ) -> Result<ir::Dtype, IrgenErrorMessage> {
        todo!()
    }

    /// Translate the register value of an expression
    /// e.g.
    /// y = x + 3
    ///
    /// %t1 = load %x0
    /// %t2 = add %t1 3
    ///
    /// we are interested in x in the right hand side
    /// we want to calculate the thing on the right hand side, so we have to load x first as t1
    fn translate_expr_rvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(id) => {
                // if its identifier then return the pointer to the value of the identifier
                let ptr = self.lookup_symbol_table_entry(&id.node.name)?;
                let ptr_dtype = ptr.dtype();
                let ptr_inner_dtype = ptr_dtype
                    .get_pointer_inner()
                    .ok_or_else(|| panic!("lookup table should return pointer type"))?;

                // when ptr points to function or an array, we don't have to load the value and
                // just return the pointer
                if ptr_inner_dtype.get_function_inner().is_some() {
                    return Ok(ptr);
                }

                if let Some(array_inner) = ptr_inner_dtype.get_array_inner() {
                    // [SELF] not sure how to do this
                    // maybe recursion to see if the inner is array. go until not array
                    // use the pointer at the last. but is it ok?
                    return self.translate_array_pointer(&ptr, &array_inner, context);
                }

                // this function insert instruction into the current context AND assign it to a
                // temp register, so it returns the temp register
                context.insert_instruction(ir::Instruction::Load { ptr })
            }
            Expression::Constant(con) => {
                let constant = ir::Constant::try_from(&con.node)
                    .expect("constant should convert to ir constant fine");

                Ok(ir::Operand::Constant(constant))
            }
            Expression::StringLiteral(_string_lit) => todo!(),
            Expression::GenericSelection(node) => todo!(),
            Expression::Member(node) => todo!(),
            Expression::Call(call_expr) => self.translate_func_call(&call_expr.node, context),
            Expression::CompoundLiteral(node) => todo!(),
            Expression::SizeOfTy(type_name) => {
                let dtype = ir::Dtype::try_from(&type_name.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let (size_of, _) = dtype
                    .size_align_of(self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                // TODO: `is_signed` must be false in the future (unsigned)
                // [UPDATE] i found the set_signed function in ir Dtype. i think this is the right
                // way to set it to unsigned
                Ok(ir::Operand::Constant(ir::Constant::int(
                    size_of as u128,
                    ir::Dtype::LONG.set_signed(false),
                )))
            }
            Expression::SizeOfVal(expr) => {
                // [SELF] translating the expr first then look at its dtype
                let rval = self.translate_expr_rvalue(&expr.node.0.node, context)?;
                let dtype = rval.dtype();
                let (size_of, _) = dtype
                    .size_align_of(self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                Ok(ir::Operand::Constant(ir::Constant::int(
                    size_of as u128,
                    ir::Dtype::LONG.set_signed(false),
                )))
            }
            Expression::AlignOf(type_name) => {
                let dtype = ir::Dtype::try_from(&type_name.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let (_, align_of) = dtype
                    .size_align_of(self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                // TODO: `is_signed` must be false in the future (unsigned)
                // [UPDATE] i found the set_signed function in ir Dtype. i think this is the right
                // way to set it to unsigned
                Ok(ir::Operand::Constant(ir::Constant::int(
                    align_of as u128,
                    ir::Dtype::LONG.set_signed(false),
                )))
            }
            Expression::UnaryOperator(node) => todo!(),
            Expression::Cast(expr) => {
                let target_dtype = ir::Dtype::try_from(&expr.node.type_name.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let target_dtype = target_dtype
                    .resolve_typedefs(&self.typedefs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let operand = self.translate_expr_rvalue(&expr.node.expression.node, context)?;

                self.translate_typecast(operand, &target_dtype, context)
            }
            Expression::BinaryOperator(binop_expr) => {
                self.translate_binary_operator_expression(&binop_expr.node, context)
            }
            Expression::Conditional(cond) => self.translate_conditional(&cond.node, context),
            Expression::Comma(nodes) => todo!(),
            Expression::OffsetOf(node) => todo!(),
            Expression::VaArg(node) => todo!(),
            Expression::Statement(node) => todo!(),
        }
    }

    /// get the location value when the expr is on the lhs of the place or when we need the location
    /// value
    ///
    /// x = 20 + 25;
    /// in this case we want x, so we have to get the location of x
    fn translate_expr_lvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(id) => self.lookup_symbol_table_entry(&id.node.name),
            Expression::Constant(_) => {
                panic!("Expression::Constant cannot be on the left hand side of the expression")
            }
            Expression::UnaryOperator(expr) => {
                // only support unary op when its indirection, other thing is not supported
                //
                // e.g. !x = false; => this is not ok
                match expr.node.operator.node {
                    // indirection
                    // *x = 64
                    // then we have to get the location of x
                    UnaryOperator::Indirection => {
                        Ok(self.translate_expr_rvalue(&expr.node.operand.node, context)?)
                    }
                    _ => panic!("unary op other than indirection is not supported"),
                }
            }
            Expression::BinaryOperator(expr) => {
                // only support binary op when its array indexing
                match expr.node.operator.node {
                    BinaryOperator::Index => {
                        todo!("translating indexing operator");
                    }
                    _ => panic!(
                        "can't use binary operator as a destination to value except indexing"
                    ),
                }
            }
            Expression::StringLiteral(_) => {
                panic!("can't use string literal on the left hand side of the assignment")
            }
            Expression::Member(node) => todo!(),
            Expression::Call(_)
            | Expression::SizeOfTy(_)
            | Expression::SizeOfVal(_)
            | Expression::AlignOf(_)
            | Expression::Cast(_)
            | Expression::Conditional(_)
            | Expression::Comma(_)
            | Expression::Statement(_) => Err(IrgenErrorMessage::Misc {
                message: "this error occured at translate_expr_lvalue".to_string(),
            }),
            _ => panic!("not supported"),
        }
    }

    /// [SELF] implemented myself
    /// get the pointer to the array
    fn translate_array_pointer(
        &self,
        ptr: &ir::Operand,
        dtype: &ir::Dtype,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        context.insert_instruction(ir::Instruction::GetElementPtr {
            ptr: ptr.clone(),
            offset: ir::Operand::constant(ir::Constant::int(0, ir::Dtype::INT)),
            dtype: dtype.clone(),
        })
    }

    /// Translate initial parameter declarations of the functions to IR.
    ///
    /// For example, given the following C function from [`foo.c`][foo]:
    ///
    /// ```C
    /// int foo(int x, int y, int z) {
    ///    if (x == y) {
    ///       return y;
    ///    } else {
    ///       return z;
    ///    }
    /// }
    /// ```
    ///
    /// The IR before this function looks roughly as follows:
    ///
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    ///   ...
    /// ```
    ///
    /// With the following arguments :
    ///
    /// ```ignore
    /// signature = FunctionSignature { ret: ir::INT, params: vec![ir::INT, ir::INT, ir::INT] }
    /// bid_init = 0
    /// name_of_params = ["x", "y", "z"]
    /// context = // omitted
    /// ```
    ///
    /// The resulting IR after this function should be roughly follows :
    ///
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///       %l0:i32:x
    ///       %l1:i32:y
    ///       %l2:i32:z
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    ///     %b0:i0:unit = store %b0:p0:i32 %l0:i32*
    ///     %b0:i1:unit = store %b0:p1:i32 %l1:i32*
    ///     %b0:i2:unit = store %b0:p2:i32 %l2:i32*
    ///   ...
    /// ```
    ///
    /// In particular, note that it is added to the local allocation list and store them to the
    /// initial phinodes.
    ///
    /// Note that the resulting IR is **a** solution. If you can think of a better way to
    /// translate parameters, feel free to do so.
    ///
    /// [foo]: https://github.com/kaist-cp/kecc-public/blob/main/examples/c/foo.c
    fn translate_parameter_decl(
        &mut self,
        signature: &ir::FunctionSignature,
        bid_init: ir::BlockId,
        name_of_params: &[String],
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        // aid is allocation id
        for (aid, (dtype, var_name)) in izip!(&signature.params, name_of_params).enumerate() {
            // [SELF] check later
            // this is the register that should be allocate
            let value = Some(ir::Operand::register(
                ir::RegisterId::arg(bid_init, aid),
                dtype.clone(),
            ));

            // this block also stores value
            let _unused = self.translate_alloc(var_name, &dtype, value, context)?;
        }
        Ok(())
    }

    fn alloc_ptr(
        &mut self,
        var: &String,
        dtype: &ir::Dtype,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let aid = self.insert_alloc(Named::new(Some(var.clone()), dtype.clone()));
        let pointer_type = ir::Dtype::pointer(dtype.clone());
        let ptr = ir::Operand::register(aid, pointer_type);
        self.insert_symbol_table_entry(var.to_string(), ptr.clone())?;
        Ok(ptr)
    }

    fn translate_alloc(
        &mut self,
        var: &String,
        dtype: &ir::Dtype,
        value: Option<ir::Operand>,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // insert the allocation
        let aid = self.insert_alloc(Named::new(Some(var.clone()), dtype.clone()));

        // int @foo(%x: int) {
        //
        // alloc xa: int -> this is inserting allocation and getting the id | xa: *int which is a
        //                  pointer type
        // store %x xa -> this is allocating value
        //
        // }

        // create the pointer that points to the allocation
        // the type of the pointer is a pointer to the type of the allocated data
        let pointer_type = ir::Dtype::pointer(dtype.clone());
        let ptr = ir::Operand::register(aid, pointer_type);
        self.insert_symbol_table_entry(var.to_string(), ptr.clone())?;

        // if the allocation also assign some values to the allocation then we need to store it
        if let Some(value) = value {
            let value = self.translate_typecast(value, &dtype, context)?;

            // store %x xa -> this is allocating value

            return context.insert_instruction(ir::Instruction::Store { ptr, value });
        }
        Ok(ptr)
    }

    /// typecast "value" to "dtype"
    /// if value already has type "dtype"
    /// just return value
    ///
    fn translate_typecast(
        &mut self,
        value: ir::Operand,
        dtype: &ir::Dtype,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let v_dtype = value.dtype();

        if &v_dtype == dtype {
            Ok(value)
        } else {
            context.insert_instruction(ir::Instruction::TypeCast {
                value,
                target_dtype: dtype.clone(),
            })
        }
    }
}

#[inline]
fn name_of_declarator(declarator: &Declarator) -> String {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(identifier) => identifier.node.name.clone(),
        DeclaratorKind::Declarator(declarator) => name_of_declarator(&declarator.node),
    }
}

#[inline]
fn name_of_params_from_function_declarator(declarator: &Declarator) -> Option<Vec<String>> {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(_) => {
            name_of_params_from_derived_declarators(&declarator.derived)
        }
        DeclaratorKind::Declarator(next_declarator) => {
            name_of_params_from_function_declarator(&next_declarator.node)
                .or_else(|| name_of_params_from_derived_declarators(&declarator.derived))
        }
    }
}

#[inline]
fn name_of_params_from_derived_declarators(
    derived_decls: &[Node<DerivedDeclarator>],
) -> Option<Vec<String>> {
    for derived_decl in derived_decls {
        match &derived_decl.node {
            DerivedDeclarator::Function(func_decl) => {
                let name_of_params = func_decl
                    .node
                    .parameters
                    .iter()
                    .map(|p| name_of_parameter_declaration(&p.node))
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                return Some(name_of_params);
            }
            DerivedDeclarator::KRFunction(_kr_func_decl) => {
                // K&R function is allowed only when it has no parameter
                return Some(Vec::new());
            }
            _ => (),
        };
    }

    None
}

#[inline]
fn name_of_parameter_declaration(parameter_declaration: &ParameterDeclaration) -> Option<String> {
    let declarator = parameter_declaration.declarator.as_ref()?;
    Some(name_of_declarator(&declarator.node))
}

#[inline]
fn is_valid_initializer(
    initializer: &Initializer,
    dtype: &ir::Dtype,
    structs: &HashMap<String, Option<ir::Dtype>>,
) -> bool {
    match initializer {
        Initializer::Expression(expr) => match dtype {
            ir::Dtype::Int { .. } | ir::Dtype::Float { .. } | ir::Dtype::Pointer { .. } => {
                match &expr.node {
                    Expression::Constant(_) => true,
                    Expression::UnaryOperator(unary) => matches!(
                        &unary.node.operator.node,
                        UnaryOperator::Minus | UnaryOperator::Plus
                    ),
                    _ => false,
                }
            }
            _ => false,
        },
        Initializer::List(items) => match dtype {
            ir::Dtype::Array { inner, .. } => items
                .iter()
                .all(|i| is_valid_initializer(&i.node.initializer.node, inner, structs)),
            ir::Dtype::Struct { name, .. } => {
                let name = name.as_ref().expect("struct should have its name");
                let struct_type = structs
                    .get(name)
                    .expect("struct type matched with `name` must exist")
                    .as_ref()
                    .expect("`struct_type` must have its definition");
                let fields = struct_type
                    .get_struct_fields()
                    .expect("`struct_type` must be struct type")
                    .as_ref()
                    .expect("`fields` must be `Some`");

                izip!(fields, items).all(|(f, i)| {
                    is_valid_initializer(&i.node.initializer.node, f.deref(), structs)
                })
            }
            _ => false,
        },
    }
}

#[inline]
fn is_invalid_structure(dtype: &ir::Dtype, structs: &HashMap<String, Option<ir::Dtype>>) -> bool {
    // When `dtype` is `Dtype::Struct`, `structs` has real definition of `dtype`
    if let ir::Dtype::Struct { name, fields, .. } = dtype {
        assert!(name.is_some() && fields.is_none());
        let name = name.as_ref().unwrap();
        structs.get(name).is_none_or(Option::is_none)
    } else {
        false
    }
}
