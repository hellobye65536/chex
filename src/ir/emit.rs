use std::{borrow::Cow, mem};

use arrayvec::ArrayVec;

use crate::{
    iota::{Iota, Pattern, SimplePattern},
    pattern, patterns,
};

pub use perm::PermEmitter;
mod perm;

#[derive(Debug, Clone, Default)]
struct PermOpt {
    ops: Vec<PermOptState>,
}

#[derive(Debug, Clone)]
enum PermOptState {
    Fish(usize),
    FishDup(usize),
    FishSlice { depth: usize, count: usize },
    DupSlice { depth: usize, count: usize },
    Perm([u8; PERMUTE_LIMIT]),
}

impl PermOpt {
    pub fn do_fish(&mut self, depth: usize) {
        if depth == 1 {
            return;
        }

        match self.ops.pop() {
            Some(PermOptState::Fish(pdepth)) => match (pdepth, depth) {
                (2, 2) => {}
                (1..=PERMUTE_LIMIT, 1..=PERMUTE_LIMIT) => {
                    let mut perm = IDENT_PERM;
                    perm_fish(&mut perm, pdepth);
                    perm_fish(&mut perm, depth);
                    self.ops.push(PermOptState::Perm(perm));
                }
                _ if pdepth == depth => {
                    self.ops.push(PermOptState::FishSlice { depth, count: 2 });
                }
                _ => {
                    self.ops.push(PermOptState::Fish(pdepth));
                    self.ops.push(PermOptState::Fish(depth));
                }
            },
            Some(PermOptState::FishDup(pdepth)) => {
                if let (1, 2) = (pdepth, depth) {
                    self.ops.push(PermOptState::FishDup(pdepth));
                } else if pdepth + 1 == depth {
                    self.do_fish(pdepth);
                    match self.ops.last() {
                        Some(PermOptState::Fish(pdepth_)) if *pdepth_ == pdepth => {
                            // heuristic: fish with depth in 1..=PERMUTE_LIMIT optimizes well
                            if let 1..=PERMUTE_LIMIT = depth {
                                self.ops.pop();
                                self.ops.push(PermOptState::FishDup(pdepth));
                                self.ops.push(PermOptState::Fish(depth));
                            } else {
                                self.ops.push(PermOptState::FishDup(1));
                            }
                        }
                        _ => self.do_fish_dup(1),
                    }
                } else {
                    self.ops.push(PermOptState::FishDup(pdepth));
                    self.ops.push(PermOptState::Fish(depth));
                }
            }
            Some(PermOptState::FishSlice {
                depth: pdepth,
                count,
            }) if depth == pdepth => {
                let count = count + 1;
                if count != depth {
                    self.ops.push(PermOptState::FishSlice { depth, count });
                }
            }
            Some(PermOptState::DupSlice { depth: 1, count }) if depth <= count => {
                self.ops.push(PermOptState::DupSlice { depth: 1, count });
            }
            Some(PermOptState::Perm(mut perm)) if depth <= PERMUTE_LIMIT => {
                perm_fish(&mut perm, depth);
                if perm != IDENT_PERM {
                    self.ops.push(PermOptState::Perm(perm));
                }
            }
            op => {
                if let Some(op) = op {
                    self.ops.push(op);
                }
                self.ops.push(PermOptState::Fish(depth));
            }
        }
    }

    pub fn do_fish_dup(&mut self, depth: usize) {
        match self.ops.pop() {
            Some(PermOptState::FishDup(pdepth)) if pdepth == depth => {
                self.ops.push(PermOptState::DupSlice { depth, count: 2 })
            }
            Some(PermOptState::DupSlice {
                depth: pdepth,
                count,
            }) if pdepth == depth => {
                self.ops.push(PermOptState::DupSlice {
                    depth,
                    count: count + 1,
                });
            }
            op => {
                if let Some(op) = op {
                    self.ops.push(op);
                }
                self.ops.push(PermOptState::FishDup(depth));
            }
        }
    }

    pub fn emit(&mut self, emitter: &mut EmbedEmitter) {
        let mut todo_stack = Vec::new();
        let mut ops = self.ops.iter();

        while let Some(op) = todo_stack.pop().as_deref().or_else(|| ops.next()) {
            match *op {
                PermOptState::Fish(2) => match ops.next() {
                    Some(PermOptState::FishDup(2)) => {
                        emitter.emit_pattern(pattern!(UndertakersGambit));
                    }
                    op => {
                        if let Some(op) = op {
                            todo_stack.push(Cow::Borrowed(op));
                        }
                        emitter.emit_pattern(pattern!(JestersGambit));
                    }
                },
                PermOptState::Fish(3) => emitter.emit_pattern(pattern!(RotationGambit)),
                PermOptState::Fish(depth) => {
                    emitter.emit_embed(Iota::Num(depth as f64));
                    emitter.emit_pattern(pattern!(FishermansGambit));
                }
                PermOptState::FishDup(1) => emitter.emit_pattern(pattern!(GeminiDecomposition)),
                PermOptState::FishDup(2) => emitter.emit_pattern(pattern!(ProspectorsGambit)),
                PermOptState::FishDup(depth) => {
                    emitter.emit_embed(Iota::Num(depth as f64));
                    emitter.emit_pattern(pattern!(FishermansGambitII));
                }
                PermOptState::FishSlice { depth: 3, count: 2 } => {
                    emitter.emit_pattern(pattern!(RotationGambitII))
                }
                PermOptState::FishSlice { depth, count } => {
                    if (1..=3).contains(&count) {
                        todo_stack.extend(itertools::repeat_n(
                            Cow::Owned(PermOptState::Fish(depth)),
                            count,
                        ));
                    } else {
                        emitter.emit_embed(Iota::Num(depth as f64));
                        emitter.emit_pattern(pattern!(FlocksGambit));

                        if count + 1 == depth {
                            emitter.emit_patterns(patterns![
                                RetrogradePurification,
                                SpeakersDecomposition,
                                IntegrationDistillation,
                                RetrogradePurification,
                            ]);
                        } else {
                            emitter.emit_pattern(pattern!(GeminiDecomposition));
                            emitter.emit_pattern(pattern!(AdditiveDistillation));
                            emitter.emit_embed(Iota::Num(depth as f64));
                            emitter.emit_embed(Iota::Num((depth + count) as f64));
                            emitter.emit_pattern(pattern!(SelectionExaltation));
                        }

                        emitter.emit_pattern(pattern!(FlocksDisintegration));
                    }
                }
                PermOptState::DupSlice { depth: 2, count } => {
                    // can be more optimal, e.g. exponentiation by squaring esque

                    let (dup, rem) = (count / 2, count % 2);

                    for _ in 0..dup {
                        emitter.emit_pattern(pattern!(DioscuriGambit));
                    }

                    match rem {
                        0 => {}
                        1 => emitter.emit_pattern(pattern!(ProspectorsGambit)),
                        _ => unreachable!("count % 2 not 0 or 1"),
                    }
                }
                PermOptState::DupSlice { depth, count } => {
                    if (1..=3).contains(&count) {
                        todo_stack.extend(itertools::repeat_n(
                            Cow::Owned(PermOptState::FishDup(depth)),
                            count,
                        ));
                    } else {
                        // can be more optimal, e.g. exponentiation by squaring esque

                        let (dup, rem) = (count / depth, count % depth);

                        emitter.emit_embed(Iota::Num(depth as f64));
                        emitter.emit_pattern(pattern!(FlocksGambit));

                        for _ in 0..dup {
                            emitter.emit_pattern(pattern!(GeminiDecomposition));
                        }

                        if rem > 0 {
                            emitter.emit_pattern(pattern!(GeminiDecomposition));
                            emitter.emit_embed(Iota::Num(0.0));
                            emitter.emit_embed(Iota::Num(rem as f64));
                            emitter.emit_pattern(pattern!(SelectionExaltation));
                            emitter.emit_pattern(pattern!(AdditiveDistillation));
                        }

                        for _ in 0..dup {
                            emitter.emit_pattern(pattern!(AdditiveDistillation));
                        }

                        emitter.emit_pattern(pattern!(FlocksDisintegration));
                    }
                }
                PermOptState::Perm(perm) => match calculate_code(&perm) {
                    0 => {}
                    1 => emitter.emit_pattern(pattern!(JestersGambit)),
                    3 => emitter.emit_pattern(pattern!(RotationGambit)),
                    4 => emitter.emit_pattern(pattern!(RotationGambitII)),
                    code => {
                        emitter.emit_embed(Iota::Num(code as f64));
                        emitter.emit_pattern(pattern!(SwindlersGambit));
                    }
                },
            }
        }
    }
}

#[derive(Debug)]
pub struct EmbedEmitter {
    inner: Vec<Iota>,
    embeds: Vec<Iota>,
}

impl EmbedEmitter {
    pub fn new(iotas: Vec<Iota>) -> Self {
        Self {
            inner: iotas,
            embeds: Vec::new(),
        }
    }

    pub fn emit_pattern(&mut self, pattern: Pattern) {
        debug_assert!(!matches!(
            pattern,
            Pattern::Simple(SimplePattern::Consideration)
                | Pattern::Simple(SimplePattern::Introspection)
                | Pattern::Simple(SimplePattern::Retrospection)
        ));

        self.resolve_embeds();
        self.inner.push(Iota::Pattern(pattern));
    }

    pub fn emit_patterns(&mut self, patterns: impl IntoIterator<Item = Pattern>) {
        patterns.into_iter().for_each(|p| self.emit_pattern(p));
    }

    pub fn emit_embed(&mut self, iota: Iota) {
        self.embeds.push(iota);
    }

    // pub fn emit_embed_list(&mut self) -> EmbedEmitter<'_> {
    //     self.emit_pattern(pattern!(Consideration));
    //     self.embeds.push(Iota::List(Vec::new()));
    //     let Iota::List(list) = self.embeds.last_mut().unwrap() else {
    //         unreachable!()
    //     };

    //     EmbedEmitter::new(list)
    // }

    fn resolve_embeds(&mut self) {
        let simple_count = self
            .embeds
            .iter()
            .filter_map(Iota::as_embed_pattern)
            .count();

        if self.embeds.len() - simple_count > 3 {
            self.inner.push(Iota::Pattern(pattern!(Consideration)));
            self.inner.push(Iota::List(mem::take(&mut self.embeds)));
            self.inner
                .push(Iota::Pattern(pattern!(FlocksDisintegration)));
        } else {
            for embed in self.embeds.drain(..) {
                if let Some(pat) = embed.as_embed_pattern() {
                    self.inner.push(Iota::Pattern(pat));
                } else {
                    self.inner.push(Iota::Pattern(pattern!(Consideration)));
                    self.inner.push(embed);
                }
            }
        }
    }

    pub fn inner(&mut self) -> &mut Vec<Iota> {
        self.resolve_embeds();
        &mut self.inner
    }

    pub fn into_inner(mut self) -> Vec<Iota> {
        self.resolve_embeds();
        self.inner
    }
}

const PERMUTE_LIMIT: usize = 12;
const IDENT_PERM: [u8; PERMUTE_LIMIT] = make_ident_perm();
const FACTORIALS: [u64; PERMUTE_LIMIT] = make_facs();

const fn make_ident_perm() -> [u8; PERMUTE_LIMIT] {
    let mut r = [0; PERMUTE_LIMIT];

    let mut i = 0;
    while i < PERMUTE_LIMIT {
        r[i] = i as u8;
        i += 1;
    }

    r
}

const fn make_facs() -> [u64; PERMUTE_LIMIT] {
    let mut r = [0; PERMUTE_LIMIT];
    r[0] = 1;

    let mut fac = 1;
    let mut i = 1;
    while i < PERMUTE_LIMIT {
        fac *= i as u64;
        r[i] = fac;
        i += 1;
    }

    r
}

fn perm_fish(perm: &mut [u8; PERMUTE_LIMIT], depth: usize) {
    perm[(PERMUTE_LIMIT - depth)..].rotate_left(1);
}

// 012
// 012 = 0:0:0 = 0
// 021 = 0:1:0 = 1
// 102 = 1:0:0 = 2
// 120 = 1:1:0 = 3
// ...
fn calculate_code(perm: &[u8; PERMUTE_LIMIT]) -> u64 {
    let mut not_taken: ArrayVec<u8, PERMUTE_LIMIT> =
        (0..u8::try_from(PERMUTE_LIMIT).unwrap()).collect();

    let mut ret = 0;

    for (perm_n, fac) in itertools::izip!(perm, FACTORIALS.into_iter().rev()) {
        let pos = not_taken
            .iter()
            .position(|v| v == perm_n)
            .expect("invalid permutation");

        not_taken.remove(pos);

        ret += u64::try_from(pos).unwrap() * fac;
    }

    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calculate_code() {
        fn extend(short: &[u8]) -> [u8; PERMUTE_LIMIT] {
            assert!((0..=PERMUTE_LIMIT).contains(&short.len()));
            let off = PERMUTE_LIMIT - short.len();

            let mut r = [0; PERMUTE_LIMIT];

            for (i, r) in r.iter_mut().enumerate().take(off) {
                *r = i.try_into().unwrap();
            }
            for (r, &s) in r.iter_mut().skip(off).zip(short) {
                *r = s + u8::try_from(off).unwrap();
            }

            r
        }

        assert_eq!(super::calculate_code(&extend(&[0])), 0);
        assert_eq!(super::calculate_code(&extend(&[1, 0])), 1);
        assert_eq!(super::calculate_code(&extend(&[1, 0, 2])), 2);
        assert_eq!(super::calculate_code(&extend(&[4, 3, 2, 1, 0])), 119);
    }

    #[test]
    #[ignore]
    fn print_perm_opt() {
        // let mut opt = PermOpt::default();

        println!(
            "{}",
            super::calculate_code(&[11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0])
        );

        // opt.do_fish(3);
        // eprintln!("{:?}", opt);
        // opt.do_fish(3);
        // eprintln!("{:?}", opt);
        // opt.do_fish(3);
        // eprintln!("{:?}", opt);
        // opt.do_fish(3);
        // eprintln!("{:?}", opt);
        // opt.do_fish(3);
        // eprintln!("{:?}", opt);
    }
}
