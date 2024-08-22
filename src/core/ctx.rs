use std::{collections::HashMap, path::PathBuf};

use crate::core::{Diagnostic, FileTag, Id, IdMap};

#[derive(Debug, Default)]
pub struct Context {
    diagnostics: Vec<Diagnostic>,
    module_map: IdMap<FileTag, PathBuf>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn emit_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic)
    }
}
