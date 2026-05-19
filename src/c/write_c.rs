use std::io::{Result, Write};

use itertools::Itertools;
use lang_c::ast::*;
use lang_c::span::Node;

use crate::write_base::*;

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
    }
}

impl<T: WriteString> WriteString for Node<T> {
    fn write_string(&self) -> String {
        self.node.write_string()
    }
}

impl WriteLine for TranslationUnit {
    /// VERY BIG HINT: You should start by understanding the [`writeln!`](https://doc.rust-lang.org/std/macro.writeln.html) macro.
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        // since TranslationUnit is a vec of node of external declaration, the first field (self.0)
        // is the vec
        for ext_decl in &self.0 {
            ext_decl.write_line(indent, write);
            writeln!(write)?;
        }
        Ok(())
    }
}

impl WriteLine for ExternalDeclaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            ExternalDeclaration::Declaration(decl) => decl.write_line(indent, write),
            ExternalDeclaration::StaticAssert(_) => panic!("doesn't support static assert"),
            ExternalDeclaration::FunctionDefinition(fdef) => fdef.write_line(indent, write),
        }
    }
}

impl WriteLine for Declaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "{};", self.write_string())?;
        Ok(())
    }
}

impl WriteLine for FunctionDefinition {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(
            write,
            "{}{}",
            self.specifiers.write_string(),
            self.declarator.write_string()
        )?;

        for decl in &self.declarations {
            decl.write_line(indent, write)?
        }

        open_block(indent, write)?;

        self.statement.write_line(indent + 1, write);

        close_block(indent, write)?;
        Ok(())
    }
}

impl WriteLine for Statement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Statement::Compound(blocks) => {
                for block in blocks {
                    match &block.node {
                        BlockItem::Declaration(decl) => decl.write_line(indent, write)?,
                        BlockItem::Statement(stmt) => stmt.write_line(indent, write)?,
                        _ => panic!("not supported"),
                    }
                }
            }
            Statement::Expression(expr) => {
                write_indent(indent, write)?;
                writeln!(write, "{};", expr.write_string())?
            }
            Statement::If(stmt) => {
                write_indent(indent, write)?;
                let condition = stmt.node.condition.write_string();
                writeln!(write, "if ({})", condition)?;
                match &stmt.node.then_statement.node {
                    Statement::Compound(_) => {
                        open_block(indent, write)?;
                        stmt.node.then_statement.write_line(indent + 1, write)?;
                        close_block(indent, write)?;
                    }
                    _ => {
                        stmt.node.then_statement.write_line(indent + 1, write)?;
                    }
                }
                if let Some(else_stmt) = &stmt.node.else_statement {
                    write_indent(indent, write)?;
                    writeln!(write, "else")?;

                    match &else_stmt.node {
                        Statement::Compound(_) => {
                            open_block(indent, write)?;
                            else_stmt.write_line(indent + 1, write)?;
                            close_block(indent, write)?;
                        }
                        _ => {
                            else_stmt.write_line(indent + 1, write)?;
                        }
                    }
                }
            }
            Statement::Switch(stmt) => {
                write_indent(indent, write)?;
                let expression = stmt.node.expression.write_string();
                writeln!(write, "switch ( {} )", expression)?;
                open_block(indent, write)?;
                stmt.node.statement.write_line(indent + 1, write)?;
                close_block(indent, write)?;
            }
            Statement::While(stmt) => {
                write_indent(indent, write)?;
                let expression = stmt.node.expression.write_string();
                writeln!(write, "while {}", expression)?;
                open_block(indent, write)?;
                stmt.node.statement.write_line(indent + 1, write)?;
                close_block(indent, write)?;
            }
            Statement::DoWhile(stmt) => {
                write_indent(indent, write)?;
                let expression = stmt.node.expression.write_string();
                writeln!(write, "do")?;
                open_block(indent, write)?;
                stmt.node.statement.write_line(indent + 1, write)?;
                close_block(indent, write)?;
                write_indent(indent, write)?;
                writeln!(write, "while {};", expression)?;
            }
            Statement::For(stmt) => {
                write_indent(indent, write)?;
                let init = stmt.node.initializer.write_string();
                let cond = stmt.node.condition.write_string();
                let inc = stmt.node.step.write_string();
                writeln!(write, "for ({};{};{})", init, cond, inc)?;
                open_block(indent, write)?;
                stmt.node.statement.write_line(indent + 1, write)?;
                close_block(indent, write)?;
            }
            Statement::Continue => {
                write_indent(indent, write)?;
                writeln!(write, "continue;")?
            }
            Statement::Break => {
                write_indent(indent, write)?;
                writeln!(write, "break;")?
            }
            Statement::Return(expr) => {
                write_indent(indent, write)?;
                writeln!(write, "return {};", expr.write_string())?
            }
            Statement::Labeled(stmt) => {
                write_indent(indent, write)?;
                match &stmt.node.label.node {
                    Label::Case(expr) => {
                        writeln!(write, "case {}:", expr.write_string())?;
                    }
                    Label::Default => writeln!(write, "default:")?,
                    _ => panic!("not supported"),
                }
                open_block(indent, write)?;
                stmt.node.statement.write_line(indent + 1, write)?;
                close_block(indent, write)?;
            }
            _ => panic!("not supported"),
        }
        Ok(())
    }
}

impl WriteString for ForInitializer {
    fn write_string(&self) -> String {
        match self {
            ForInitializer::Empty => "".to_string(),
            ForInitializer::Expression(expr) => expr.write_string(),
            ForInitializer::Declaration(decl) => decl.write_string(),
            _ => panic!("not supported"),
        }
    }
}

impl WriteString for Vec<Node<DeclarationSpecifier>> {
    fn write_string(&self) -> String {
        self.iter().map(WriteString::write_string).join(" ")
    }
}

impl WriteString for Initializer {
    fn write_string(&self) -> String {
        match self {
            Initializer::Expression(expr) => expr.write_string(),
            Initializer::List(init) => format!(
                "{{ {} }}",
                init.iter()
                    .map(|item| {
                        let init = item.node.initializer.write_string();
                        if item.node.designation.is_empty() {
                            init
                        } else {
                            let des = item
                                .node
                                .designation
                                .iter()
                                .map(WriteString::write_string)
                                .collect_vec()
                                .join(", ");
                            format!("{} = {}", des, init)
                        }
                    })
                    .join(", ")
            ),
        }
    }
}

impl WriteString for Designator {
    fn write_string(&self) -> String {
        match self {
            Designator::Index(expr) => format!("[{}]", expr.write_string()),
            Designator::Member(id) => format!(".{}", id.write_string()),
            Designator::Range(range) => format!(
                "[{}..{}]",
                range.node.from.write_string(),
                range.node.to.write_string()
            ),
        }
    }
}

impl WriteString for IntegerBase {
    fn write_string(&self) -> String {
        match self {
            IntegerBase::Decimal => "".to_string(),
            IntegerBase::Octal => "0".to_string(),
            IntegerBase::Hexadecimal => "0x".to_string(),
            IntegerBase::Binary => "0b".to_string(),
        }
    }
}

impl WriteString for FloatBase {
    fn write_string(&self) -> String {
        match self {
            FloatBase::Decimal => "".to_string(),
            FloatBase::Hexadecimal => "0x".to_string(),
        }
    }
}

impl WriteString for IntegerSize {
    fn write_string(&self) -> String {
        todo!("not important")
    }
}

impl WriteString for IntegerSuffix {
    fn write_string(&self) -> String {
        assert!(!self.imaginary, "can't be imaginary");
        format!(
            "{}{}",
            match self.size {
                IntegerSize::Int => "".to_string(),
                IntegerSize::Long => "L".to_string(),
                IntegerSize::LongLong => "LL".to_string(),
            },
            if (self.unsigned) {
                "u".to_string()
            } else {
                "".to_string()
            }
        )
    }
}

impl WriteString for FloatSuffix {
    fn write_string(&self) -> String {
        assert!(!self.imaginary, "can't be imaginary");
        match self.format {
            FloatFormat::Float => "F".to_string(),
            FloatFormat::Double => "".to_string(),
            FloatFormat::LongDouble => "L".to_string(),
            _ => panic!("not supported"),
        }
    }
}

impl WriteString for Expression {
    fn write_string(&self) -> String {
        match self {
            Expression::Identifier(id) => id.node.name.to_string(),
            Expression::Constant(con) => match &con.node {
                Constant::Integer(integer) => {
                    format!(
                        "{}{}{}",
                        integer.base.write_string(),
                        integer.number,
                        integer.suffix.write_string()
                    )
                }
                Constant::Float(float) => {
                    format!(
                        "{}{}{}",
                        float.base.write_string(),
                        float.number,
                        float.suffix.write_string()
                    )
                }
                Constant::Character(s) => s.to_string(),
            },
            Expression::Member(expr) => match expr.node.operator.node {
                MemberOperator::Direct => {
                    format!(
                        "{}.{}",
                        expr.node.expression.write_string(),
                        expr.node.identifier.write_string()
                    )
                }
                MemberOperator::Indirect => {
                    format!(
                        "{}->{}",
                        expr.node.expression.write_string(),
                        expr.node.identifier.write_string()
                    )
                }
            },
            Expression::Call(expr) => {
                format!(
                    "{}({})",
                    expr.node.callee.write_string(),
                    expr.node
                        .arguments
                        .iter()
                        .map(WriteString::write_string)
                        .collect_vec()
                        .join(", ")
                )
            }
            Expression::SizeOfTy(expr) => {
                format!("sizeof ({})", expr.node.0.write_string())
            }
            Expression::SizeOfVal(expr) => {
                format!("sizeof {}", expr.node.0.write_string())
            }
            Expression::AlignOf(expr) => {
                format!("_Alignof ({})", expr.node.0.write_string())
            }
            Expression::UnaryOperator(expr) => expr.write_string(),
            Expression::Cast(expr) => {
                format!(
                    "({}) {}",
                    expr.node.type_name.write_string(),
                    expr.node.expression.write_string()
                )
            }
            Expression::BinaryOperator(expr) => expr.write_string(),
            Expression::Conditional(expr) => {
                let cond = expr.node.clone();
                format!(
                    "({} ? {} : {})",
                    cond.condition.write_string(),
                    cond.then_expression.write_string(),
                    cond.else_expression.write_string()
                )
            }
            Expression::Comma(expr) => {
                format!(
                    "({})",
                    expr.iter()
                        .map(WriteString::write_string)
                        .collect_vec()
                        .join(", ")
                )
            }
            _ => panic!("not supported"),
        }
    }
}

impl WriteString for BinaryOperatorExpression {
    fn write_string(&self) -> String {
        let lhs = self.lhs.write_string();
        let rhs = self.rhs.write_string();
        let operator = match self.operator.node {
            BinaryOperator::Index => return format!("{}[{}]", lhs, rhs),
            BinaryOperator::Multiply => "*".to_string(),
            BinaryOperator::Divide => "/".to_string(),
            BinaryOperator::Modulo => "%".to_string(),
            BinaryOperator::Plus => "+".to_string(),
            BinaryOperator::Minus => "-".to_string(),
            BinaryOperator::ShiftLeft => "<<".to_string(),
            BinaryOperator::ShiftRight => ">>".to_string(),
            BinaryOperator::Less => "<".to_string(),
            BinaryOperator::Greater => ">".to_string(),
            BinaryOperator::LessOrEqual => "<=".to_string(),
            BinaryOperator::GreaterOrEqual => ">=".to_string(),
            BinaryOperator::Equals => "==".to_string(),
            BinaryOperator::NotEquals => "!=".to_string(),
            BinaryOperator::BitwiseAnd => "&".to_string(),
            BinaryOperator::BitwiseXor => "^".to_string(),
            BinaryOperator::BitwiseOr => "|".to_string(),
            BinaryOperator::LogicalAnd => "&&".to_string(),
            BinaryOperator::LogicalOr => "||".to_string(),
            BinaryOperator::Assign => "=".to_string(),
            BinaryOperator::AssignMultiply => "*=".to_string(),
            BinaryOperator::AssignDivide => "/=".to_string(),
            BinaryOperator::AssignModulo => "%=".to_string(),
            BinaryOperator::AssignPlus => "+=".to_string(),
            BinaryOperator::AssignMinus => "-=".to_string(),
            BinaryOperator::AssignShiftLeft => "<<=".to_string(),
            BinaryOperator::AssignShiftRight => ">>=".to_string(),
            BinaryOperator::AssignBitwiseAnd => "&=".to_string(),
            BinaryOperator::AssignBitwiseXor => "^=".to_string(),
            BinaryOperator::AssignBitwiseOr => "|=".to_string(),
        };

        format!("({} {} {})", lhs, operator, rhs)
    }
}

impl WriteString for UnaryOperatorExpression {
    fn write_string(&self) -> String {
        let operand = self.operand.write_string();
        match self.operator.node {
            UnaryOperator::PostIncrement => format!("{}++", operand),
            UnaryOperator::PostDecrement => format!("{}--", operand),
            UnaryOperator::PreIncrement => format!("++{}", operand),
            UnaryOperator::PreDecrement => format!("--{}", operand),
            UnaryOperator::Address => format!("&{}", operand),
            UnaryOperator::Indirection => format!("*{}", operand),
            UnaryOperator::Plus => format!("+{}", operand),
            UnaryOperator::Minus => format!("-{}", operand),
            UnaryOperator::Complement => format!("~{}", operand),
            UnaryOperator::Negate => format!("!{}", operand),
        }
    }
}

// pub struct TypeName {
//     pub specifiers: Vec<Node<SpecifierQualifier>>,
//     pub declarator: Option<Node<Declarator>>,
// }
impl WriteString for TypeName {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect_vec()
                .join(" "),
            self.declarator.write_string()
        )
    }
}

impl WriteString for SpecifierQualifier {
    fn write_string(&self) -> String {
        match self {
            SpecifierQualifier::TypeSpecifier(typ) => typ.write_string(),
            SpecifierQualifier::TypeQualifier(qual) => qual.write_string(),
            _ => panic!("not supported"),
        }
    }
}

impl WriteString for Identifier {
    fn write_string(&self) -> String {
        self.name.clone()
    }
}

impl WriteString for Declaration {
    fn write_string(&self) -> String {
        format!(
            "{}{}",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect_vec()
                .join(" "),
            self.declarators
                .iter()
                .map(WriteString::write_string)
                .collect_vec()
                .join(", "),
        )
    }
}

impl WriteString for DeclarationSpecifier {
    fn write_string(&self) -> String {
        match self {
            DeclarationSpecifier::StorageClass(spec) => match spec.node {
                StorageClassSpecifier::Typedef => "typedef".to_string(),
                StorageClassSpecifier::Extern => "extern".to_string(),
                StorageClassSpecifier::Static => "static".to_string(),
                StorageClassSpecifier::ThreadLocal => "_Thread_Local".to_string(),
                StorageClassSpecifier::Auto => "auto".to_string(),
                StorageClassSpecifier::Register => "register".to_string(),
            },
            DeclarationSpecifier::TypeSpecifier(spec) => spec.write_string(),
            DeclarationSpecifier::TypeQualifier(qual) => qual.write_string(),
            _ => panic!("not supported"),
        }
    }
}

impl WriteString for TypeSpecifier {
    fn write_string(&self) -> String {
        match self {
            TypeSpecifier::Void => "void".to_string(),
            TypeSpecifier::Char => "char".to_string(),
            TypeSpecifier::Short => "short".to_string(),
            TypeSpecifier::Int => "int".to_string(),
            TypeSpecifier::Long => "long".to_string(),
            TypeSpecifier::Float => "float".to_string(),
            TypeSpecifier::Double => "double".to_string(),
            TypeSpecifier::Signed => "signed".to_string(),
            TypeSpecifier::Unsigned => "unsigned".to_string(),
            TypeSpecifier::Bool => "_Bool".to_string(),
            TypeSpecifier::Struct(st) => st.write_string(),
            TypeSpecifier::TypedefName(name) => name.node.write_string(),
            _ => panic!("not supported"),
        }
    }
}

impl WriteString for StructType {
    fn write_string(&self) -> String {
        assert_ne!(self.kind.node, StructKind::Union);
        let id = self.identifier.write_string();
        if let Some(decls) = &self.declarations {
            let decl = decls.iter().map(WriteString::write_string).join(" ");
            format!("struct {} {{ {} }}", id, decl)
        } else {
            format!("struct {}", id)
        }
    }
}

impl WriteString for StructDeclaration {
    fn write_string(&self) -> String {
        match self {
            StructDeclaration::Field(f) => {
                let spec = f
                    .node
                    .specifiers
                    .iter()
                    .map(WriteString::write_string)
                    .join(" ");
                let decl = f
                    .node
                    .declarators
                    .iter()
                    .map(WriteString::write_string)
                    .join(" ");

                format!("{} {};", spec, decl)
            }
            StructDeclaration::StaticAssert(_) => {
                panic!("not supported StructDeclaration::StaticAssert")
            }
        }
    }
}

impl WriteString for StructDeclarator {
    fn write_string(&self) -> String {
        let decl = self.declarator.write_string();
        if let Some(bit) = &self.bit_width {
            format!("{} : {}", decl, bit.write_string())
        } else {
            decl
        }
    }
}

impl WriteString for TypeQualifier {
    fn write_string(&self) -> String {
        match self {
            TypeQualifier::Const => "const".to_string(),
            _ => panic!("not supported"),
        }
    }
}

impl WriteString for InitDeclarator {
    fn write_string(&self) -> String {
        if let Some(init) = &self.initializer {
            format!(
                "{} = {}",
                self.declarator.write_string(),
                self.initializer.write_string()
            )
        } else {
            self.declarator.write_string()
        }
    }
}

impl WriteString for Declarator {
    fn write_string(&self) -> String {
        assert!(self.extensions.is_empty(), "extension should be empty");
        let kind = match &self.kind.node {
            DeclaratorKind::Abstract => "".to_string(),
            DeclaratorKind::Identifier(id) => format!(" {}", id.write_string()),
            DeclaratorKind::Declarator(decl) => format!("({})", decl.write_string()),
        };

        let mut inner: String = kind.clone();

        for der in self.derived.iter() {
            match &der.node {
                DerivedDeclarator::Pointer(pqs) => {
                    let pointer = pqs
                        .iter()
                        .map(|pq| match &pq.node {
                            PointerQualifier::TypeQualifier(typ) => typ.write_string(),
                            _ => panic!("not supported"),
                        })
                        .join(" ");
                    inner = format!("*{}{}", pointer, inner);
                }
                DerivedDeclarator::Array(arr) => {
                    let typ = arr
                        .node
                        .qualifiers
                        .iter()
                        .map(WriteString::write_string)
                        .join(" ");
                    let size = match &arr.node.size {
                        ArraySize::VariableExpression(expr) => expr.write_string(),
                        _ => panic!("not supported"),
                    };
                    inner = format!("{}{}[{}]", typ, inner, size);
                }
                DerivedDeclarator::Function(fdec) => {
                    assert_eq!(fdec.node.ellipsis, Ellipsis::None);
                    let param = fdec
                        .node
                        .parameters
                        .iter()
                        .map(WriteString::write_string)
                        .join(", ");
                    inner = format!("{}({})", inner, param);
                }
                DerivedDeclarator::KRFunction(ids) => {
                    let identifier = ids.iter().map(WriteString::write_string).join(",");
                    inner = format!("{}({})", inner, identifier);
                }
                _ => panic!("unsupported"),
            };
        }
        inner
    }
}

impl WriteString for ParameterDeclaration {
    fn write_string(&self) -> String {
        assert!(self.extensions.is_empty(), "extension should be empty");
        let specs = self
            .specifiers
            .iter()
            .map(WriteString::write_string)
            .join(" ");
        if let Some(decl) = &self.declarator {
            format!("{}{}", specs, decl.write_string())
        } else {
            specs
        }
    }
}

fn write_indent(indent: usize, write: &mut dyn Write) -> Result<()> {
    let size = "  ";
    for _ in 0..indent {
        write!(write, "{}", size)?;
    }
    Ok(())
}

fn open_block(indent: usize, write: &mut dyn Write) -> Result<()> {
    write_indent(indent, write)?;
    writeln!(write, "{{")?;
    Ok(())
}

fn close_block(indent: usize, write: &mut dyn Write) -> Result<()> {
    write_indent(indent, write)?;
    writeln!(write, "}}")?;
    Ok(())
}
