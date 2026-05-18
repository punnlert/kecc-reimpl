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
        todo!()
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
        todo!()
    }
}

impl WriteString for IntegerSuffix {
    fn write_string(&self) -> String {
        assert!(!self.imaginary);
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
        assert!(!self.imaginary);
        format!(
            "{}",
            match self.format {
                FloatFormat::Float => "",
                FloatFormat::Double => "F",
                FloatFormat::LongDouble => "L",
                _ => panic!("not supported"),
            }
        )
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
                        integer.number.to_string(),
                        integer.suffix.write_string()
                    )
                }
                Constant::Float(float) => {
                    format!(
                        "{}{}{}",
                        float.base.write_string(),
                        float.number.to_string(),
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
                    "{} ? {} : {}",
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

        format!("{}{}{}", lhs, operator, rhs)
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
            "{} {}",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect_vec()
                .join(" "),
            self.declarators
                .iter()
                .map(WriteString::write_string)
                .collect_vec()
                .join(" "),
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
            _ => panic!("not supported"),
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
        format!(
            "{} {}",
            self.declarator.write_string(),
            self.initializer.write_string()
        )
    }
}

impl WriteString for Declarator {
    fn write_string(&self) -> String {
        todo!()
    }
}

fn write_indent(indent: usize, write: &mut dyn Write) -> Result<()> {
    for _ in 0..indent {
        write!(write, " ")?;
    }
    Ok(())
}
