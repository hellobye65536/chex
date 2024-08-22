use std::iter;

use itertools::Itertools;

use crate::{
    core::{Id, IdGen, IdMap},
    iota::{Iota, Pattern},
    pattern, patterns, UsizeToU8,
};

mod emit;
use emit::{EmbedEmitter, PermEmitter};

pub enum VarTag {}
pub type Var = Id<VarTag>;
pub type VarMap<T> = IdMap<VarTag, T>;

type Binding = Option<Var>;

#[derive(Debug, Clone)]
pub struct Block {
    args: Vec<Binding>,
    captures: Vec<Binding>,
    stmts: Vec<Stmt>,
    ret: Vec<Var>,
    effect: Effect,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    Iota {
        binding: Binding,
        iota: Iota,
        call_eff: Effect,
    },
    Block {
        binding: Binding,
        block: Box<Block>,
        captures: Vec<Var>,
    },
    Call {
        bindings: Vec<Binding>,
        args: Vec<Var>,
        block: Var,
    },
}

impl Stmt {
    pub fn effect(&self, call_effs: &VarMap<Effect>) -> Effect {
        match self.kind {
            StmtKind::Call { block, .. } => call_effs.get(block).copied().unwrap_or_default(),
            _ => Effect::Pure,
        }
    }

    pub fn bindings(&self) -> impl Iterator<Item = Binding> + Clone + '_ {
        use stmt_iter::StmtBindings;

        match self.kind {
            StmtKind::Iota { binding, .. } => StmtBindings::Once(Some(binding)),
            StmtKind::Block { binding, .. } => StmtBindings::Once(Some(binding)),
            StmtKind::Call { ref bindings, .. } => StmtBindings::Slice(bindings.iter()),
        }
    }

    pub fn args(&self) -> impl Iterator<Item = Var> + Clone + '_ {
        use stmt_iter::StmtArgs;

        match self.kind {
            StmtKind::Iota { .. } => StmtArgs::Once(None),
            StmtKind::Block { ref captures, .. } => StmtArgs::Slice(captures.iter()),
            StmtKind::Call {
                ref args, block, ..
            } => StmtArgs::Call(args.iter(), Some(block)),
        }
    }
}

mod stmt_iter {
    use super::{Binding, Var};

    #[derive(Debug, Clone)]
    pub enum StmtBindings<'a> {
        Once(Option<Binding>),
        Slice(std::slice::Iter<'a, Binding>),
    }

    impl<'a> Iterator for StmtBindings<'a> {
        type Item = Binding;

        fn next(&mut self) -> Option<Self::Item> {
            match self {
                StmtBindings::Once(v) => v.take(),
                StmtBindings::Slice(v) => v.next().copied(),
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum StmtArgs<'a> {
        Once(Option<Var>),
        Slice(std::slice::Iter<'a, Var>),
        Call(std::slice::Iter<'a, Var>, Option<Var>),
    }

    impl<'a> Iterator for StmtArgs<'a> {
        type Item = Var;

        fn next(&mut self) -> Option<Self::Item> {
            match self {
                StmtArgs::Once(v) => v.take(),
                StmtArgs::Slice(v) => v.next().copied(),
                StmtArgs::Call(args, block) => args.next().copied().or_else(|| block.take()),
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Effect {
    #[default]
    Effectful,
    Impure,
    Pure,
}

pub fn lower_ir(block: Block, var_gen: &IdGen<VarTag>) -> Vec<Iota> {
    let mut use_count = VarMap::with_capacity(var_gen.generated_count());
    count_uses(&block, &mut use_count);

    emit_block(block, &mut use_count)
}

fn emit_block(block: Block, use_count: &mut VarMap<u32>) -> Vec<Iota> {
    let mut iotas = Vec::new();
    let mut var_stack = itertools::chain!(&block.args, &block.captures)
        .copied()
        .collect_vec();

    if !block.captures.is_empty() {
        iotas.push(Iota::Pattern(pattern!(Consideration)));
        iotas.push(Iota::Null);
    }

    let mut emitter = EmbedEmitter::new(iotas);

    if block.captures.len() > 1 {
        emitter.emit_pattern(pattern!(FlocksDisintegration));
    }

    let mut emitter = PermEmitter::new(emitter);

    for stmt in block.stmts {
        match stmt.kind {
            StmtKind::Iota { binding, iota, .. } => {
                if let Some(binding) = binding {
                    emitter.emit_embed(iota);
                    var_stack.push(Some(binding));
                }
            }
            StmtKind::Block {
                binding,
                block,
                captures,
            } => {
                if let Some(binding) = binding {
                    emitter.emit_embed(Iota::List(emit_block(*block, use_count)));
                    let len = captures.len();
                    if len > 0 {
                        emitter.emit_embed(Iota::Num(1.0));

                        emit_args(
                            &mut var_stack,
                            use_count,
                            2,
                            captures.iter().copied(),
                            &mut emitter,
                        );

                        if len > 1 {
                            emitter.emit_embed(Iota::Num(len as f64));
                            emitter.emit_op(patterns![FlocksGambit], len + 1, 1);
                        }
                        emitter.emit_op(patterns![SurgeonsExaltation], 3, 1);
                    }

                    var_stack.push(Some(binding));
                }
            }
            StmtKind::Call {
                bindings,
                args,
                block,
            } => {
                emit_args(
                    &mut var_stack,
                    use_count,
                    0,
                    args.iter().copied().chain([block]),
                    &mut emitter,
                );

                emitter.emit_op(patterns![HermesGambit], args.len() + 1, bindings.len());

                var_stack.extend(bindings);
            }
        }
    }

    emitter.into_inner().into_inner()
}

fn emit_args(
    var_stack: &mut Vec<Option<Id<VarTag>>>,
    use_count: &mut VarMap<u32>,
    extra: usize,
    args: impl Iterator<Item = Var> + Clone,
    emitter: &mut PermEmitter,
) {
    for var in args.clone() {
        use_count[var] -= 1;
    }

    let first_arg = var_stack
        .iter()
        .position(|var| var.is_some_and(|var| args.clone().contains(&var)))
        .expect("stack doesn't contain arguments");

    let mut perm = var_stack[first_arg..]
        .iter()
        .positions(|var| var.is_some_and(|var| use_count[var] != 0))
        .map(usize::into_u8)
        .collect_vec();

    let size = var_stack.len() - first_arg;

    perm.extend((size.into_u8()..).take(extra));

    let size = size + extra;

    perm.extend(args.map(|var| {
        var_stack[first_arg..]
            .iter()
            .position(|&var_| var_ == Some(var))
            .unwrap()
            .into_u8()
    }));

    let mut i = 0;
    var_stack.retain(|var| {
        i += 1;
        i <= first_arg || var.is_some()
    });

    emitter.emit_perm(size, 0, perm);
}

fn count_uses(block: &Block, use_count: &mut VarMap<u32>) {
    for stmt in &block.stmts {
        for arg in stmt.args() {
            *use_count.get_or_insert_default(arg) += 1;
        }

        if let StmtKind::Block { ref block, .. } = stmt.kind {
            count_uses(block, use_count);
        }
    }

    for &var in &block.ret {
        *use_count.get_or_insert_default(var) += 1;
    }
}

fn compute_call_eff(block: &Block, call_eff: &mut VarMap<Effect>) {
    for stmt in &block.stmts {
        match stmt.kind {
            StmtKind::Iota {
                binding: Some(var),
                call_eff: eff,
                ..
            } => {
                call_eff.insert(var, eff);
            }
            StmtKind::Block {
                binding: Some(var),
                ref block,
                ..
            } => {
                call_eff.insert(var, block.effect);

                compute_call_eff(block, call_eff);
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum UseType {
    Once { stmt_index: usize },
    Many,
}

fn compute_use_type(block: &Block, use_types: &mut VarMap<UseType>) {
    for (i, stmt) in block.stmts.iter().enumerate() {
        for arg in stmt.args() {
            match use_types.get_mut(arg) {
                Some(UseType::Once { stmt_index: i_ }) if *i_ == i => {}
                Some(r) => *r = UseType::Many,
                None => {
                    use_types.insert(arg, UseType::Once { stmt_index: i });
                }
            }

            if let StmtKind::Block { block, .. } = &stmt.kind {
                compute_use_type(block, use_types);
            }
        }
    }
}

fn compute_stmt_map(block: &Block, stmt_map: &mut VarMap<usize>) {
    for (i, stmt) in block.stmts.iter().enumerate() {
        for var in stmt.bindings().flatten() {
            stmt_map.insert(var, i);
        }

        if let StmtKind::Block { ref block, .. } = stmt.kind {
            compute_stmt_map(block, stmt_map);
        }
    }
}

#[cfg(test)]
mod tests {}
