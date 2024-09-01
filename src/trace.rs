use std::collections::BTreeSet;

use crate::{
  binparser::{BinParse, BinParser, Ptr, TagPtr},
  idx::IdxVec,
  mk_id, Tree,
};
use dbg_pls::DebugPls;

pub trait HasBinParse<I> {
  fn parse(&mut self, bp: &BinParser<'_>, p: TagPtr) -> I;
}
macro_rules! mk_id_mapping {
  ($($ty:ident,)*) => {
    $(impl<'a, C: HasBinParse<$ty>> BinParse<'a, C> for $ty {
      fn parse(ctx: &mut C, bp: &BinParser<'a>, p: TagPtr) -> Self {
        ctx.parse(bp, p)
      }
    })*
    pub trait IdMapping: $(HasBinParse<$ty> +)* {}
    mk_id! { $($ty(u32),)* }
  }
}
mk_id_mapping! {
  StringId,
  ClassId,
  SortId,
  IndexNameId,
  TypeId,
  TermId,
}
mk_id! {
  ProofId(u32),
  AssumptionId(u32),
}

type ProofPtr = TagPtr;

#[derive(Clone, Debug, DebugPls, Hash, PartialEq, Eq)]
pub enum Type {
  Type(StringId, Vec<TypeId>),
  Free(StringId, SortId),
  Var(IndexNameId, SortId),
}

impl<C: IdMapping> BinParse<'_, C> for Type {
  fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    match bp.get_enum(p) {
      (0, &[x, s]) => Self::Free(bp.parse(ctx, x), bp.parse(ctx, s)),
      (1, &[i, s]) => Self::Var(bp.parse(ctx, i), bp.parse(ctx, s)),
      (2, &[s, tys]) => Self::Type(bp.parse(ctx, s), bp.parse(ctx, tys)),
      _ => panic!(),
    }
  }
}

#[derive(Clone, Debug, DebugPls, Hash, PartialEq, Eq)]
pub enum Term {
  Const(StringId, TypeId),
  Free(StringId, TypeId),
  Var(IndexNameId, TypeId),
  Bound(u32),
  Abs(StringId, TypeId, TermId),
  App(TermId, TermId),
}

impl<C: IdMapping> BinParse<'_, C> for Term {
  fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    match bp.get_enum(p) {
      (0, &[e1, e2]) => Self::App(bp.parse(ctx, e1), bp.parse(ctx, e2)),
      (1, &[x, ty, e]) => Self::Abs(bp.parse(ctx, x), bp.parse(ctx, ty), bp.parse(ctx, e)),
      (2, &[i]) => Self::Bound(bp.parse(ctx, i)),
      (3, &[c, ty]) => Self::Const(bp.parse(ctx, c), bp.parse(ctx, ty)),
      (4, &[x, ty]) => Self::Free(bp.parse(ctx, x), bp.parse(ctx, ty)),
      (5, &[x, ty]) => Self::Var(bp.parse(ctx, x), bp.parse(ctx, ty)),
      _ => panic!(),
    }
  }
}

#[derive(Copy, Clone, Debug, DebugPls, PartialEq, Eq)]
pub struct MaxIdx(pub u32);

impl MaxIdx {
  pub const NONE: Self = Self(0);
  pub fn var(v: u32) -> MaxIdx {
    Self(v + 1)
  }
  pub fn max(self, other: MaxIdx) -> Self {
    Self(self.0.max(other.0))
  }
  pub fn fold_max(iter: impl Iterator<Item = Self>) -> Self {
    Self(iter.fold(0, |a, b| a.max(b.0)))
  }
}
// impl<C> BinParse<'_, C> for MaxIdx {
//   fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
//     Self((i32::parse_v2(t) + 1) as u32)
//   }
// }

pub struct Table<K, V>(Vec<(K, V)>);

impl<'a, C, K: BinParse<'a, C>, V: BinParse<'a, C>> BinParse<'a, C> for Table<K, V> {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, p: TagPtr) -> Self {
    fn accum<'a, C, K: BinParse<'a, C>, V: BinParse<'a, C>>(
      ctx: &mut C, bp: &BinParser<'a>, out: &mut Vec<(K, V)>, p: TagPtr,
    ) {
      #![allow(non_upper_case_globals)]
      const Branch2: u32 = 0;
      const Branch3: u32 = 1;
      const Empty: u32 = 2;
      const Leaf1: u32 = 3;
      const Leaf2: u32 = 4;
      const Leaf3: u32 = 5;
      const Size: u32 = 6;
      match bp.get_enum(p) {
        (Empty, &[]) => {}
        (Leaf1, &[k1, v1]) => out.push((bp.parse(ctx, k1), bp.parse(ctx, v1))),
        (Leaf2, &[kv1, kv2]) => {
          out.push(bp.parse(ctx, kv1));
          out.push(bp.parse(ctx, kv2))
        }
        (Leaf3, &[kv1, kv2, kv3]) => {
          out.push(bp.parse(ctx, kv1));
          out.push(bp.parse(ctx, kv2));
          out.push(bp.parse(ctx, kv3))
        }
        (Branch2, &[t1, kv, t2]) => {
          accum(ctx, bp, out, t1);
          out.push(bp.parse(ctx, kv));
          accum(ctx, bp, out, t2);
        }
        (Branch3, &[args]) => {
          let &[t1, kv1, t2, kv2, t3] = bp.get(p.as_ptr()).as_tuple_n();
          accum(ctx, bp, out, t1);
          out.push(bp.parse(ctx, kv1));
          accum(ctx, bp, out, t2);
          out.push(bp.parse(ctx, kv2));
          accum(ctx, bp, out, t3);
        }
        (Size, &[_, p]) => accum(ctx, bp, out, p),
        _ => panic!(),
      }
    }
    let mut out = vec![];
    accum(ctx, bp, &mut out, p);
    Table(out)
  }
}

#[derive(Debug, DebugPls)]
pub struct Subst {
  pub tysubst: Box<[(IndexNameId, SortId, TypeId)]>,
  pub subst: Box<[(IndexNameId, TypeId, TermId)]>,
}

impl Subst {
  pub fn from_assoc<C: IdMapping>(
    ctx: &mut C, bp: &BinParser<'_>, tsub: TagPtr, sub: TagPtr,
  ) -> Self {
    Subst {
      tysubst: bp.parse_list(tsub).map(|p| bp.parse(ctx, p)).map(|((a, b), c)| (a, b, c)).collect(),
      subst: bp.parse_list(sub).map(|p| bp.parse(ctx, p)).map(|((a, b), c)| (a, b, c)).collect(),
    }
  }
  pub fn from_env<C: IdMapping>(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    let (tenv, tyenv, _maxidx): (Table<_, _>, Table<_, _>, TagPtr) = bp.parse(ctx, p);
    Self {
      tysubst: tyenv.0.into_iter().map(|(a, (b, c))| (a, b, c)).collect(),
      subst: tenv.0.into_iter().map(|(a, (b, c))| (a, b, c)).collect(),
    }
  }
}

type ThmId = u32;

#[derive(Debug, DebugPls)]
pub struct GeneralizeArgs {
  pub tfrees: Vec<StringId>,
  pub frees: Vec<StringId>,
  pub idx: u32,
}

#[derive(Debug, DebugPls)]
pub struct ConstrainArgs {
  pub shyps: Box<[SortId]>,
  pub hyps: Box<[TermId]>,
  pub prop: TermId,
}

#[derive(Debug, DebugPls)]
pub struct BicomposeArgs {
  pub env: Subst,
  pub tpairs: Box<[(TermId, TermId)]>,
  pub nsubgoal: u32,
  pub flatten: bool,
  pub as_: Box<[TermId]>,
  pub a_: Option<TermId>,
  pub n: u32,
  pub nlift: u32,
}
impl<C: IdMapping> BinParse<'_, C> for BicomposeArgs {
  fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    let &[env, tpairs, nsubgoal, flatten, as_, a_, n, nlift] = bp.get(p.as_ptr()).as_tuple_n();
    Self {
      env: Subst::from_env(ctx, bp, env),
      tpairs: bp.parse(ctx, tpairs),
      nsubgoal: bp.parse(ctx, nsubgoal),
      flatten: bp.parse(ctx, flatten),
      as_: bp.parse(ctx, as_),
      a_: bp.parse(ctx, a_),
      n: bp.parse(ctx, n),
      nlift: bp.parse(ctx, nlift),
    }
  }
}

#[derive(Clone, Copy, Debug, DebugPls)]
pub enum AxiomSource {
  Forgot,
  Prev,
}

// impl<C> BinParse<'_, C> for AxiomSource {
//   fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
//     let Tree::Elem(s, _, ts) = t else { panic!() };
//     match (&**s, &**ts) {
//       (b"?", []) => Self::Forgot,
//       (b"P", []) => Self::Prev,
//       _ => panic!(),
//     }
//   }
// }
#[derive(Debug, DebugPls)]
pub enum Proof {
  Sorry,
  Hyp(TermId),
  ImpIntr(TermId, ProofId),
  ImpElim(ProofId, ProofId),
  ForallIntr(TermId, ProofId),
  ForallElim(TermId, ProofId),
  Axiom(StringId, TermId, AxiomSource),
  Oracle(StringId, TermId),
  Refl(TermId),
  Symm(ProofId),
  Trans(ProofId, ProofId),
  BetaNorm(TermId),
  BetaHead(TermId),
  Eta(TermId),
  EtaLong(TermId),
  StripSHyps(Box<[SortId]>, ProofId),
  AbsRule(TermId, ProofId),
  AppRule(ProofId, ProofId),
  EqIntr(ProofId, ProofId),
  EqElim(ProofId, ProofId),
  FlexFlex(Box<Subst>, ProofId),
  Generalize(Box<GeneralizeArgs>, ProofId),
  Instantiate(Box<Subst>, ProofId),
  Trivial,
  OfClass(TypeId, StringId),
  Thm(ThmId),
  ConstrainThm(Box<ConstrainArgs>, ThmId),
  Varify(Box<[(StringId, SortId, IndexNameId, SortId)]>, ProofId),
  LegacyFreezeT(ProofId),
  Lift(TermId, u32, ProofId),
  IncrIndexes(u32, ProofId),
  Assumption(u32, u32, ProofId),
  EqAssumption(u32, ProofId),
  Rotate(u32, u32, ProofId),
  PermutePrems(u32, u32, ProofId),
  Bicompose(Box<BicomposeArgs>, ProofId, ProofId),
  Pruned,
}

#[allow(non_upper_case_globals)]
pub mod proof {
  use super::*;

  pub const AbsRule: u32 = 0;
  pub const AppRule: u32 = 1;
  pub const Assumption: u32 = 2;
  pub const Axiom: u32 = 3;
  pub const BetaHead: u32 = 4;
  pub const BetaNorm: u32 = 5;
  pub const Bicompose: u32 = 6;
  pub const ConstrainThm: u32 = 7;
  pub const EqAssumption: u32 = 8;
  pub const EqElim: u32 = 9;
  pub const EqIntr: u32 = 10;
  pub const Eta: u32 = 11;
  pub const EtaLong: u32 = 12;
  pub const FlexFlex: u32 = 13;
  pub const ForallElim: u32 = 14;
  pub const ForallIntr: u32 = 15;
  pub const Generalize: u32 = 16;
  pub const Hyp: u32 = 17;
  pub const ImpElim: u32 = 18;
  pub const ImpIntr: u32 = 19;
  pub const IncrIndexes: u32 = 20;
  pub const Instantiate: u32 = 21;
  pub const LegacyFreezeT: u32 = 22;
  pub const Lift: u32 = 23;
  pub const OfClass: u32 = 24;
  pub const Oracle: u32 = 25;
  pub const PermutePrems: u32 = 26;
  pub const Pruned: u32 = 27;
  pub const Refl: u32 = 28;
  pub const Rotate: u32 = 29;
  pub const Sorry: u32 = 30;
  pub const StripSHyps: u32 = 31;
  pub const Symm: u32 = 32;
  pub const Thm: u32 = 33;
  pub const Trans: u32 = 34;
  pub const Trivial: u32 = 35;
  pub const Varify: u32 = 36;

  pub const END: u32 = 37;

  pub fn num_subproofs(tag: u32) -> usize {
    match tag {
      Sorry | Hyp | Axiom | Oracle | Refl | BetaNorm | BetaHead | Eta | EtaLong | Trivial
      | OfClass | Thm | ConstrainThm | Pruned => 0,
      ImpIntr | ForallIntr | ForallElim | Symm | StripSHyps | AbsRule | FlexFlex | Generalize
      | Instantiate | Varify | LegacyFreezeT | Lift | IncrIndexes | Assumption | EqAssumption
      | Rotate | PermutePrems => 1,
      ImpElim | Trans | AppRule | EqIntr | EqElim | Bicompose => 2,
      END.. => panic!(),
    }
  }

  pub fn subproofs<'a>(bp: &BinParser<'a>, p: ProofPtr) -> &'a [ProofPtr] {
    let (tag, args) = bp.get_enum(p);
    &args[args.len() - num_subproofs(tag)..]
  }
}

// impl<C> BinParse<'_, C> for Proof {
//   fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
//     let Tree::Elem(s, _, ts) = t else { panic!() };
//     match (&**s, &**ts) {
//       (b"?", []) => Self::Sorry,
//       (b"X", [a]) => Self::Hyp(<_>::parse_v2(a)),
//       (b"i", [a, p]) => Self::ImpIntr(<_>::parse_v2(a), <_>::parse_v2(p)),
//       (b"I", [p, q]) => Self::ImpElim(<_>::parse_v2(p), <_>::parse_v2(q)),
//       (b"f", [a, p]) => Self::ForallIntr(<_>::parse_v2(a), <_>::parse_v2(p)),
//       (b"F", [p, a]) => Self::ForallElim(<_>::parse_v2(p), <_>::parse_v2(a)),
//       (b"A", [a, b, s]) => Self::Axiom(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(s)),
//       (b"O", [a, b]) => Self::Oracle(<_>::parse_v2(a), <_>::parse_v2(b)),
//       (b"=", [a]) => Self::Refl(<_>::parse_v2(a)),
//       (b"-", [p]) => Self::Symm(<_>::parse_v2(p)),
//       (b"+", [p, q]) => Self::Trans(<_>::parse_v2(p), <_>::parse_v2(q)),
//       (b"B", [a]) => Self::BetaNorm(<_>::parse_v2(a)),
//       (b"b", [a]) => Self::BetaHead(<_>::parse_v2(a)),
//       (b"h", [a]) => Self::Eta(<_>::parse_v2(a)),
//       (b"H", [a]) => Self::EtaLong(<_>::parse_v2(a)),
//       (b"p", [s, p]) => Self::StripSHyps(<_>::parse_v2(s), <_>::parse_v2(p)),
//       (b"l", [a, p]) => Self::AbsRule(<_>::parse_v2(a), <_>::parse_v2(p)),
//       (b"c", [p, q]) => Self::AppRule(<_>::parse_v2(p), <_>::parse_v2(q)),
//       (b"e", [p, q]) => Self::EqIntr(<_>::parse_v2(p), <_>::parse_v2(q)),
//       (b"E", [p, q]) => Self::EqElim(<_>::parse_v2(p), <_>::parse_v2(q)),
//       (b"x", [e, p]) => Self::FlexFlex(<_>::parse_v2(e), <_>::parse_v2(p)),
//       (b"G", [a, b, c, p]) => Self::Generalize(
//         Box::new(GeneralizeArgs {
//           tfrees: <_>::parse_v2(a),
//           frees: <_>::parse_v2(b),
//           idx: <_>::parse_v2(c),
//         }),
//         <_>::parse_v2(p),
//       ),
//       (b"N", [a, b, p]) => Self::Instantiate(
//         Box::new(Subst { tysubst: <_>::parse_v2(a), subst: <_>::parse_v2(b) }),
//         <_>::parse_v2(p),
//       ),
//       (b"t", []) => Self::Trivial,
//       (b"o", [a, b]) => Self::OfClass(<_>::parse_v2(a), <_>::parse_v2(b)),
//       (b"T", [i]) => Self::Thm(<_>::parse_v2(i)),
//       (b"K", [i, sh, h, t]) => {
//         let args = Box::new(ConstrainArgs {
//           shyps: <_>::parse_v2(sh),
//           hyps: <_>::parse_v2(h),
//           prop: <_>::parse_v2(t),
//         });
//         Self::ConstrainThm(args, <_>::parse_v2(i))
//       }
//       (b"V", [a, p]) => Self::Varify(<_>::parse_v2(a), <_>::parse_v2(p)),
//       (b"g", [p]) => Self::LegacyFreezeT(<_>::parse_v2(p)),
//       (b"L", [a, b, p]) => Self::Lift(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(p)),
//       (b"k", [a, p]) => Self::IncrIndexes(<_>::parse_v2(a), <_>::parse_v2(p)),
//       (b"a", [p, a]) => Self::Assumption(<_>::parse_v2(p), <_>::parse_v2(a)),
//       (b"q", [p]) => Self::EqAssumption(<_>::parse_v2(p)),
//       (b"R", [a, b, p]) => Self::Rotate(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(p)),
//       (b"P", [a, b, p]) => Self::PermutePrems(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(p)),
//       (b"C", [env, tpairs, nsubgoal, flatten, as_, a_, n, nlift, p, q]) => Self::Bicompose(
//         Box::new(BicomposeArgs {
//           env: <_>::parse_v2(env),
//           tpairs: <_>::parse_v2(tpairs),
//           nsubgoal: <_>::parse_v2(nsubgoal),
//           flatten: <_>::parse_v2(flatten),
//           as_: <_>::parse_v2(as_),
//           a_: <_>::parse_v2(a_),
//           n: <_>::parse_v2(n),
//           nlift: <_>::parse_v2(nlift),
//         }),
//         <_>::parse_v2(p),
//         <_>::parse_v2(q),
//       ),
//       (b"!", []) => Self::Pruned,
//       _ => panic!(),
//     }
//   }
// }

#[derive(Debug, DebugPls)]
pub struct Position {
  pub line: u32,
  pub offset: (u32, u32),
  pub label: StringId,
  pub file: StringId,
  pub id: StringId,
}
impl<C: HasBinParse<StringId>> BinParse<'_, C> for Position {
  fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    let &[line, props, offset, end_offset] = bp.get(p.as_ptr()).as_tuple_n();
    let (id, file, label) = bp.parse(ctx, props);
    Self {
      line: bp.parse(ctx, line),
      offset: (bp.parse(ctx, offset), bp.parse(ctx, end_offset)),
      label,
      file,
      id,
    }
  }
}

#[derive(Debug, DebugPls)]
pub struct ThmName {
  pub name: StringId,
  pub i: u32,
  pub pos: Position,
}
impl<C: HasBinParse<StringId>> BinParse<'_, C> for ThmName {
  fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    let ((name, i), pos) = bp.parse(ctx, p);
    Self { name, i, pos }
  }
}

#[derive(Debug, DebugPls)]
pub struct Header {
  pub serial: ThmId,
  pub command_pos: Position,
  pub theory_name: StringId,
  pub thm_name: ThmName,
  pub prop: TermId,
  // pub types: Option<Box<[TypeId]>>,
}
impl<C: IdMapping> BinParse<'_, C> for Header {
  fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    let &[prop, types, serial, thm_name, command_pos, theory_name] =
      bp.get(p.as_ptr()).as_tuple_n();
    assert!(<Option<Box<[TypeId]>>>::parse(ctx, bp, types).is_none());
    Self {
      serial: bp.parse(ctx, serial),
      command_pos: bp.parse(ctx, command_pos),
      theory_name: bp.parse(ctx, theory_name),
      thm_name: bp.parse(ctx, thm_name),
      prop: bp.parse(ctx, prop),
      // types: <_>::parse_v2(types),
    }
  }
}

#[derive(Debug, DebugPls)]
pub struct ThmTrace {
  pub header: Header,
  pub root: ProofPtr,
  pub unconstrain_var_map: Vec<(TypeId, TypeId)>,
  pub unconstrain_shyps: u32,
  pub unconstrain_hyps: Vec<TermId>,
}
impl<C: IdMapping> BinParse<'_, C> for ThmTrace {
  fn parse(ctx: &mut C, bp: &BinParser<'_>, p: TagPtr) -> Self {
    let &[header, uc_var_map, uc_shyps, uc_hyps, root] = bp.get(p.as_ptr()).as_tuple_n();
    // println!("strings: {strings:?}");
    // println!("sorts: {sorts:?}");
    // println!("indexnames: {indexnames:?}");
    // println!("types: {types:?}");
    // println!("terms: {terms:?}");
    // println!("proofs: {proofs:?}");
    // println!("assumptions: {assumptions:?}");
    Self {
      header: bp.parse(ctx, header),
      root,
      unconstrain_var_map: bp.parse(ctx, uc_var_map),
      unconstrain_shyps: bp.parse(ctx, uc_shyps),
      unconstrain_hyps: bp.parse(ctx, uc_hyps),
    }
  }
}

impl ThmTrace {
  pub fn get_uses(bp: &BinParser<'_>, p: TagPtr) -> BTreeSet<u32> {
    let &[_, _, _, _, root] = bp.get(p.as_ptr()).as_tuple_n();
    let mut visited = BTreeSet::new();
    let mut thms = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(p) = stack.pop() {
      if visited.insert(p) {
        let (tag, args) = bp.get_enum(p);
        let i = proof::num_subproofs(tag);
        if i == 0 {
          if let proof::Thm | proof::ConstrainThm = tag {
            thms.insert(args[0].as_uint());
          }
        } else {
          stack.extend(&args[args.len() - i..])
        }
      }
    }
    thms
  }
}
// impl Context {
//   pub fn count_uses(&self) -> IdxVec<ProofId, u8> {
//     let mut uses = IdxVec::<_, u8>::from_default(self.proofs.len());
//     for pf in &self.proofs.0 {
//       match *pf {
//         Proof::Sorry
//         | Proof::Hyp(_)
//         | Proof::Axiom(_, _, _)
//         | Proof::Oracle(_, _)
//         | Proof::Refl(_)
//         | Proof::BetaNorm(_)
//         | Proof::BetaHead(_)
//         | Proof::Eta(_)
//         | Proof::EtaLong(_)
//         | Proof::Trivial
//         | Proof::OfClass(_, _)
//         | Proof::Thm(_)
//         | Proof::ConstrainThm(_, _)
//         | Proof::Pruned => {}

//         Proof::ImpIntr(_, p)
//         | Proof::ForallIntr(_, p)
//         | Proof::ForallElim(p, _)
//         | Proof::Symm(p)
//         | Proof::StripSHyps(_, p)
//         | Proof::AbsRule(_, p)
//         | Proof::FlexFlex(_, p)
//         | Proof::Generalize(_, p)
//         | Proof::Instantiate(_, p)
//         | Proof::Varify(_, p)
//         | Proof::LegacyFreezeT(p)
//         | Proof::Lift(_, _, p)
//         | Proof::IncrIndexes(_, p)
//         | Proof::Rotate(_, _, p)
//         | Proof::PermutePrems(_, _, p) => uses[p] = uses[p].saturating_add(1),

//         Proof::ImpElim(p, q)
//         | Proof::Trans(p, q)
//         | Proof::AppRule(p, q)
//         | Proof::EqIntr(p, q)
//         | Proof::EqElim(p, q)
//         | Proof::Bicompose(_, p, q) => {
//           uses[p] = uses[p].saturating_add(1);
//           uses[q] = uses[q].saturating_add(1);
//         }

//         Proof::Assumption(a, _) | Proof::EqAssumption(a) => {
//           let p = self.assumptions[a].0;
//           uses[p] = uses[p].saturating_add(1)
//         }
//       }
//     }
//     uses
//   }
// }
