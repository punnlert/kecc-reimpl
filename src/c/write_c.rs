use std::io::{Result, Write};

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
        todo!()
    }
}

impl WriteString for Initializer {
    fn write_string(&self) -> String {
        todo!()
    }
}
