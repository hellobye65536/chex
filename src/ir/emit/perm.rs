use std::{borrow::Cow, cmp::min, mem};

use bitvec::vec::BitVec;
use itertools::Itertools;

use crate::{
    iota::{Iota, Pattern}, pattern, UsizeToU8
};

use super::{EmbedEmitter, PermOpt};

#[derive(Debug)]
pub struct PermEmitter {
    inner: EmbedEmitter,
    state: PermEmitterState,
}

impl PermEmitter {
    pub fn new(inner: EmbedEmitter) -> Self {
        PermEmitter {
            inner,
            state: Default::default(),
        }
    }

    pub fn from_inner(inner: EmbedEmitter) -> PermEmitter {
        PermEmitter {
            inner,
            state: Default::default(),
        }
    }

    pub fn emit_perm(&mut self, size: usize, depth: usize, perm: Vec<u8>) {
        let mut nperm = InstPerm { size, depth, perm };
        match &mut self.state {
            PermEmitterState::Init(perm) => {
                *perm = perm.fuse(&nperm);
            }
            PermEmitterState::Consumer(state) => {
                nperm.depth += state.depth;
                state.perm = state.perm.fuse(&nperm);
            }
            PermEmitterState::Producer(state) => {
                state.perm = state.perm.fuse(&nperm);
            }
        }
    }

    pub fn emit_op(&mut self, pats: impl IntoIterator<Item = Pattern>, args: usize, rets: usize) {
        let pats = pats.into_iter();
        match mem::take(&mut self.state) {
            PermEmitterState::Init(mut perm) => {
                if rets == 0 {
                    self.state = PermEmitterState::Consumer(Consumer {
                        perm,
                        depth: args,
                        ops: itertools::chain!(
                            [ConsumerOp::Indicator(args)],
                            pats.map(ConsumerOp::Pattern),
                        )
                        .collect(),
                    });
                } else if args == 0 {
                    perm.depth += rets;
                    self.state = PermEmitterState::Producer(Producer {
                        perm,
                        ops: itertools::chain!(
                            pats.map(ProducerOp::Pattern),
                            [ProducerOp::Indicator(rets)],
                        )
                        .collect(),
                    });
                } else {
                    perm.emit(&mut self.inner);
                    pats.for_each(|pat| self.inner.emit_pattern(pat));
                }
            }
            PermEmitterState::Consumer(mut state) => {
                if rets == 0 {
                    state.depth += args;
                    state.ops.push(ConsumerOp::Indicator(args));
                    state.ops.extend(pats.map(ConsumerOp::Pattern));
                    self.state = PermEmitterState::Consumer(state);
                } else {
                    state.emit(&mut self.inner);
                    self.emit_op(pats, args, rets);
                }
            }
            PermEmitterState::Producer(mut state) => {
                if args == 0 {
                    state.perm.depth += rets;
                    state.ops.extend(pats.map(ProducerOp::Pattern));
                    state.ops.push(ProducerOp::Indicator(rets));
                    self.state = PermEmitterState::Producer(state);
                } else {
                    state.emit(&mut self.inner);
                    self.emit_op(pats, args, rets);
                }
            }
        }
    }

    pub fn emit_embed(&mut self, iota: Iota) {
        match mem::take(&mut self.state) {
            PermEmitterState::Init(mut perm) => {
                perm.depth += 1;
                self.state = PermEmitterState::Producer(Producer {
                    perm,
                    ops: vec![ProducerOp::Embed(iota)],
                });
            }
            PermEmitterState::Producer(mut state) => {
                state.perm.depth += 1;
                state.ops.push(ProducerOp::Embed(iota));
                self.state = PermEmitterState::Producer(state);
            }
            state => {
                state.emit(&mut self.inner);
                self.emit_embed(iota);
            }
        }
    }

    fn resolve_state(&mut self) {
        mem::take(&mut self.state).emit(&mut self.inner)
    }

    pub fn inner(&mut self) -> &mut EmbedEmitter {
        self.resolve_state();
        &mut self.inner
    }

    pub fn into_inner(mut self) -> EmbedEmitter {
        self.resolve_state();
        self.inner
    }
}

#[derive(Debug, Clone)]
enum PermEmitterState {
    Init(InstPerm),
    Consumer(Consumer),
    Producer(Producer),
}

impl PermEmitterState {
    fn emit(self, emitter: &mut EmbedEmitter) {
        match self {
            PermEmitterState::Init(perm) => perm.emit(emitter),
            PermEmitterState::Consumer(consumer) => consumer.emit(emitter),
            PermEmitterState::Producer(producer) => producer.emit(emitter),
        }
    }
}

impl Default for PermEmitterState {
    fn default() -> Self {
        Self::Init(InstPerm::default())
    }
}

#[derive(Debug, Clone)]
struct Consumer {
    perm: InstPerm,
    depth: usize,
    ops: Vec<ConsumerOp>,
}

impl Consumer {
    fn emit(self, emitter: &mut EmbedEmitter) {
        let Consumer {
            mut perm,
            depth: _,
            ops,
        } = self;

        perm.simplify();
        let mut ops = ops.into_iter();
        for op in ops.by_ref() {
            match op {
                ConsumerOp::Indicator(args) => {
                    if args <= perm.depth {
                        perm.depth -= args;
                    } else {
                        break;
                    }
                }
                ConsumerOp::Pattern(pat) => emitter.emit_pattern(pat),
            }
        }
        perm.emit(emitter);
        ops.for_each(|op| op.emit(emitter));
    }
}

#[derive(Debug, Clone)]
enum ConsumerOp {
    Indicator(usize),
    Pattern(Pattern),
}

impl ConsumerOp {
    fn emit(self, emitter: &mut EmbedEmitter) {
        match self {
            ConsumerOp::Indicator(_) => {}
            ConsumerOp::Pattern(pat) => emitter.emit_pattern(pat),
        }
    }
}

#[derive(Debug, Clone)]
struct Producer {
    perm: InstPerm,
    ops: Vec<ProducerOp>,
}

impl Producer {
    fn emit(self, emitter: &mut EmbedEmitter) {
        let Producer { mut perm, ops } = self;

        perm.simplify();
        let trailing = ops
            .iter()
            .take_while(|op| {
                let rets = match **op {
                    ProducerOp::Indicator(rets) => rets,
                    ProducerOp::Pattern(_) => 0,
                    ProducerOp::Embed(_) => 1,
                };
                if rets <= perm.depth {
                    perm.depth -= rets;
                    true
                } else {
                    false
                }
            })
            .count();

        let len = ops.len();
        let mut ops = ops.into_iter();
        (&mut ops)
            .take(len - trailing)
            .for_each(|op| op.emit(emitter));
        perm.emit(emitter);
        ops.for_each(|op| op.emit(emitter));
    }
}

#[derive(Debug, Clone)]
enum ProducerOp {
    Indicator(usize),
    Pattern(Pattern),
    Embed(Iota),
}

impl ProducerOp {
    fn emit(self, emitter: &mut EmbedEmitter) {
        match self {
            ProducerOp::Indicator(_) => {}
            ProducerOp::Pattern(pat) => emitter.emit_pattern(pat),
            ProducerOp::Embed(iota) => emitter.emit_embed(iota),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct InstPerm {
    size: usize,
    depth: usize,
    perm: Vec<u8>,
}

impl InstPerm {
    fn emit(self, emitter: &mut EmbedEmitter) {
        let mut used: BitVec = BitVec::with_capacity(self.size + self.depth);
        used.resize(self.size, false);
        self.perm.iter().for_each(|&v| used.set(v.into(), true));

        let mut stack: Vec<_> = used.iter_ones().map(usize::into_u8).collect();

        if used.not_all() {
            used.resize(self.size + self.depth, true);
            emitter.emit_pattern(pattern!(BookkeepersGambit: Cow::Owned(used)));
        }

        let mut elide_move: BitVec = BitVec::repeat(false, self.size);
        let mut perm_rest = self.perm.iter().copied().peekable();
        for elem in stack.iter().copied() {
            let Some(&perm_elem) = perm_rest.peek() else {
                break;
            };

            if elem == perm_elem {
                elide_move.set(elem.into(), true);
                perm_rest.next();
            }
        }

        if perm_rest.peek().is_none() {
            return;
        }

        let mut opt = PermOpt::default();

        let mut top_stack = Vec::new();
        for perm_elem in perm_rest {
            if let Some((pos, _)) = top_stack
                .iter()
                .enumerate()
                .rev()
                .find(|&(i, &v)| v == perm_elem)
            {
                opt.do_fish_dup(top_stack.len() - pos);
            } else {
                let (pos, _) = stack
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|&(i, &v)| v == perm_elem)
                    .expect("invalid permutation");

                if elide_move[usize::from(perm_elem)] {
                    opt.do_fish_dup(stack.len() - pos + self.depth + top_stack.len());
                } else {
                    opt.do_fish(stack.len() - pos + self.depth + top_stack.len());
                    stack.remove(pos);
                }
            };

            top_stack.push(perm_elem);
        }

        for _ in 0..self.depth {
            opt.do_fish(top_stack.len() + self.depth);
        }

        opt.emit(emitter);
    }

    fn fuse(&self, next: &InstPerm) -> InstPerm {
        // self:
        // self.size + self.depth
        // self.perm.len() + self.depth

        // next:
        // next.size + next.depth
        // next.perm.len() + next.depth

        let depth = min(self.depth, next.depth);

        let self_full_size = self.full_size();
        let self_out_full_size = self.out_full_size();
        let next_full_size = next.full_size();
        let next_out_full_size = next.out_full_size();

        let size_adj = next_full_size.saturating_sub(self_out_full_size);
        let full_size = self_full_size + size_adj;
        let size = full_size - depth;

        let out_full_size = self_out_full_size.saturating_sub(next_full_size) + next_out_full_size;
        let out_size = out_full_size - depth;

        let mut perm = Vec::new();

        if next_full_size >= self_out_full_size {
            let offset = next_full_size - self_out_full_size;
            let offsetu8 = u8::try_from(offset).unwrap();

            perm.extend(next.perm.iter().map(|&np| {
                let nps = usize::from(np);

                match nps.checked_sub(offset).map(|i| self.perm.get(i)) {
                    Some(Some(&stack_elem)) => stack_elem + offsetu8,
                    Some(None) => u8::try_from(nps - self.perm.len() + self.size).unwrap(),
                    None => np,
                }
            }));

            perm.extend(
                self.perm[self.perm.len() - next.depth.saturating_sub(self.depth)..]
                    .iter()
                    .map(|v| v + offsetu8),
            );
        } else {
            let offset = self_out_full_size - next_full_size;

            perm.extend_from_slice(&self.perm[..offset]);
            perm.extend(next.perm.iter().map(|&np| {
                let nps = usize::from(np);

                if let Some(&stack_elem) = self.perm.get(nps + offset) {
                    stack_elem
                } else {
                    (nps + offset - self.perm.len() + self.size).into_u8()
                }
            }));

            perm.extend_from_slice(
                &self.perm[self.perm.len() - next.depth.saturating_sub(self.depth)..],
            );
        }

        debug_assert_eq!(perm.len(), out_size);

        InstPerm { size, depth, perm }
    }

    fn simplify(&mut self) {
        let mut seen: BitVec = BitVec::repeat(false, self.size);
        let (left, right) = self
            .perm
            .iter()
            .copied()
            .filter(|&v| seen.replace(usize::from(v), true))
            .minmax()
            .into_option()
            .unwrap_or(((self.size - 1).into_u8(), 0));

        let left_rm = itertools::izip!(0..left, &self.perm)
            .take_while(|(a, b)| a == *b)
            .count();

        let right_rm = itertools::izip!(
            (right + 1..self.size.into_u8()).rev(),
            self.perm.iter().rev()
        )
        .take_while(|(a, b)| a == *b)
        .count();

        if left_rm + right_rm >= self.perm.len() {
            self.perm.clear();
            self.size = 0;
            self.depth = 0;
            return;
        }

        self.perm.truncate(self.perm.len() - right_rm);
        self.perm.drain(0..left_rm);
        self.perm
            .iter_mut()
            .for_each(|r| *r -= left_rm.into_u8());

        self.size -= left_rm;
        self.size -= right_rm;
        self.depth += right_rm;
    }

    fn full_size(&self) -> usize {
        self.size + self.depth
    }

    fn out_full_size(&self) -> usize {
        self.perm.len() + self.depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn perm_fuse() {
        // 0 1 2 3 -> 1 0 1 2 3
        let perm = InstPerm {
            size: 2,
            depth: 2,
            perm: vec![1, 0, 1],
        };

        // 1 0 1 2 3 -> 1 0 2 1 3
        let next = InstPerm {
            size: 2,
            depth: 1,
            perm: vec![1, 0],
        };

        assert_eq!(
            perm.fuse(&next),
            InstPerm {
                size: 3,
                depth: 1,
                perm: vec![1, 0, 2, 1],
            }
        );

        // 0 1 -> 0 1 1
        let perm = InstPerm {
            size: 1,
            depth: 0,
            perm: vec![0, 0],
        };

        // 0 1 1 -> 0 0 1 1
        let next = InstPerm {
            size: 1,
            depth: 2,
            perm: vec![0, 0],
        };

        assert_eq!(
            perm.fuse(&next),
            InstPerm {
                size: 2,
                depth: 0,
                perm: vec![0, 0, 1, 1],
            }
        );
    }

    #[test]
    fn perm_simplify() {
        let mut perm = InstPerm {
            size: 3,
            depth: 1,
            perm: vec![0, 1, 1, 2],
        };

        perm.simplify();

        assert_eq!(
            perm,
            InstPerm {
                size: 1,
                depth: 2,
                perm: vec![0, 0],
            }
        );

        let mut perm = InstPerm {
            size: 3,
            depth: 1,
            perm: vec![0, 0, 1, 1, 2],
        };

        perm.simplify();

        assert_eq!(
            perm,
            InstPerm {
                size: 2,
                depth: 2,
                perm: vec![0, 0, 1, 1],
            }
        );
    }
}
