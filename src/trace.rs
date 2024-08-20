use crate::{idx::IdxVec, mk_id, Parse, Tree};
use dbg_pls::DebugPls;

mk_id! {
  StringId(u32),
  SortId(u32),
  IndexNameId(u32),
  TypeId(u32),
  TermId(u32),
  ProofId(u32),
  AssumptionId(u32),
}
// pub type ClassId = StringId;

#[derive(Clone, Debug, DebugPls, Hash, PartialEq, Eq)]
pub enum Type {
  Type(StringId, Vec<TypeId>),
  Free(StringId, SortId),
  Var(IndexNameId, SortId),
}

impl Parse<'_> for Type {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let Tree::Elem(s, _, ts) = t else { panic!() };
    match (&**s, &**ts) {
      (b"T", [s, tys]) => Self::Type(<_>::parse_v2(s), <_>::parse_v2(tys)),
      (b"F", [x, s]) => Self::Free(<_>::parse_v2(x), <_>::parse_v2(s)),
      (b"V", [i, s]) => Self::Var(<_>::parse_v2(i), <_>::parse_v2(s)),
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

impl Parse<'_> for Term {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let Tree::Elem(s, _, ts) = t else { panic!() };
    match (&**s, &**ts) {
      (b"C", [c, ty]) => Self::Const(<_>::parse_v2(c), <_>::parse_v2(ty)),
      (b"F", [x, ty]) => Self::Const(<_>::parse_v2(x), <_>::parse_v2(ty)),
      (b"V", [x, ty]) => Self::Var(<_>::parse_v2(x), <_>::parse_v2(ty)),
      (b"B", [i]) => Self::Bound(<_>::parse_v2(i)),
      (b"L", [x, ty, e]) => Self::Abs(<_>::parse_v2(x), <_>::parse_v2(ty), <_>::parse_v2(e)),
      (b"A", [e1, e2]) => Self::App(<_>::parse_v2(e1), <_>::parse_v2(e2)),
      _ => panic!(),
    }
  }
}

#[derive(Copy, Clone, Debug, DebugPls)]
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
impl Parse<'_> for MaxIdx {
  fn parse_v2(t: &Tree<'_>) -> Self {
    Self((i32::parse_v2(t) + 1) as u32)
  }
}

#[derive(Debug, DebugPls)]
pub struct Env {
  maxidx: MaxIdx,
  tenv: Box<[(StringId, u32, TypeId, TermId)]>,
  tyenv: Box<[(StringId, u32, SortId, TypeId)]>,
}

impl Parse<'_> for Env {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let (maxidx, tenv, tyenv) = <_>::parse_v2(t);
    Self { maxidx, tenv, tyenv }
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
pub struct InstantiateArgs {
  pub tysubst: Box<[(IndexNameId, SortId, TypeId)]>,
  pub subst: Box<[(IndexNameId, TypeId, TermId)]>,
}

#[derive(Debug, DebugPls)]
pub struct ConstrainArgs {
  pub shyps: Box<[SortId]>,
  pub hyps: Box<[TermId]>,
  pub prop: TermId,
}

#[derive(Debug, DebugPls)]
pub struct BicomposeArgs {
  pub env: Env,
  pub smax: MaxIdx,
  pub flatten: bool,
  pub bs: Box<[TermId]>,
  pub as_: Box<[TermId]>,
  pub a_: Option<TermId>,
  pub old_as: Box<[TermId]>,
  pub n: u32,
  pub nlift: u32,
}

#[derive(Clone, Copy, Debug, DebugPls)]
pub enum AxiomSource {
  Forgot,
  Prev,
}

impl Parse<'_> for AxiomSource {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let Tree::Elem(s, _, ts) = t else { panic!() };
    match (&**s, &**ts) {
      (b"?", []) => Self::Forgot,
      (b"P", []) => Self::Prev,
      _ => panic!(),
    }
  }
}
#[derive(Debug, DebugPls)]
pub enum Proof {
  Sorry,
  Hyp(TermId),
  ImpIntr(TermId, ProofId),
  ImpElim(ProofId, ProofId),
  ForallIntr(TermId, ProofId),
  ForallElim(ProofId, TermId),
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
  FlexFlex(Box<Env>, ProofId),
  Generalize(Box<GeneralizeArgs>, ProofId),
  Instantiate(Box<InstantiateArgs>, ProofId),
  Trivial,
  OfClass(TypeId, StringId),
  Thm(ThmId),
  ConstrainThm(Box<ConstrainArgs>, ThmId),
  Varify(Box<[(StringId, SortId, IndexNameId, SortId)]>, ProofId),
  LegacyFreezeT(ProofId),
  Lift(TermId, u32, ProofId),
  IncrIndexes(u32, ProofId),
  Assumption(AssumptionId, u32),
  EqAssumption(AssumptionId),
  Rotate(u32, u32, ProofId),
  PermutePrems(u32, u32, ProofId),
  Bicompose(Box<BicomposeArgs>, ProofId, ProofId),
  Pruned,
}

impl Parse<'_> for Proof {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let Tree::Elem(s, _, ts) = t else { panic!() };
    match (&**s, &**ts) {
      (b"?", []) => Self::Sorry,
      (b"X", [a]) => Self::Hyp(<_>::parse_v2(a)),
      (b"i", [a, p]) => Self::ImpIntr(<_>::parse_v2(a), <_>::parse_v2(p)),
      (b"I", [p, q]) => Self::ImpElim(<_>::parse_v2(p), <_>::parse_v2(q)),
      (b"f", [a, p]) => Self::ForallIntr(<_>::parse_v2(a), <_>::parse_v2(p)),
      (b"F", [p, a]) => Self::ForallElim(<_>::parse_v2(p), <_>::parse_v2(a)),
      (b"A", [a, b, s]) => Self::Axiom(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(s)),
      (b"O", [a, b]) => Self::Oracle(<_>::parse_v2(a), <_>::parse_v2(b)),
      (b"=", [a]) => Self::Refl(<_>::parse_v2(a)),
      (b"-", [p]) => Self::Symm(<_>::parse_v2(p)),
      (b"+", [p, q]) => Self::Trans(<_>::parse_v2(p), <_>::parse_v2(q)),
      (b"B", [a]) => Self::BetaNorm(<_>::parse_v2(a)),
      (b"b", [a]) => Self::BetaHead(<_>::parse_v2(a)),
      (b"h", [a]) => Self::Eta(<_>::parse_v2(a)),
      (b"H", [a]) => Self::EtaLong(<_>::parse_v2(a)),
      (b"p", [s, p]) => Self::StripSHyps(<_>::parse_v2(s), <_>::parse_v2(p)),
      (b"l", [a, p]) => Self::AbsRule(<_>::parse_v2(a), <_>::parse_v2(p)),
      (b"c", [p, q]) => Self::AppRule(<_>::parse_v2(p), <_>::parse_v2(q)),
      (b"e", [p, q]) => Self::EqIntr(<_>::parse_v2(p), <_>::parse_v2(q)),
      (b"E", [p, q]) => Self::EqElim(<_>::parse_v2(p), <_>::parse_v2(q)),
      (b"x", [e, p]) => Self::FlexFlex(<_>::parse_v2(e), <_>::parse_v2(p)),
      (b"G", [a, b, c, p]) => Self::Generalize(
        Box::new(GeneralizeArgs {
          tfrees: <_>::parse_v2(a),
          frees: <_>::parse_v2(b),
          idx: <_>::parse_v2(c),
        }),
        <_>::parse_v2(p),
      ),
      (b"N", [a, b, p]) => Self::Instantiate(
        Box::new(InstantiateArgs { tysubst: <_>::parse_v2(a), subst: <_>::parse_v2(b) }),
        <_>::parse_v2(p),
      ),
      (b"t", []) => Self::Trivial,
      (b"o", [a, b]) => Self::OfClass(<_>::parse_v2(a), <_>::parse_v2(b)),
      (b"T", [i]) => Self::Thm(<_>::parse_v2(i)),
      (b"K", [i, sh, h, t]) => {
        let args = Box::new(ConstrainArgs {
          shyps: <_>::parse_v2(sh),
          hyps: <_>::parse_v2(h),
          prop: <_>::parse_v2(t),
        });
        Self::ConstrainThm(args, <_>::parse_v2(i))
      }
      (b"V", [a, p]) => Self::Varify(<_>::parse_v2(a), <_>::parse_v2(p)),
      (b"g", [p]) => Self::LegacyFreezeT(<_>::parse_v2(p)),
      (b"L", [a, b, p]) => Self::Lift(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(p)),
      (b"k", [a, p]) => Self::IncrIndexes(<_>::parse_v2(a), <_>::parse_v2(p)),
      (b"a", [p, a]) => Self::Assumption(<_>::parse_v2(p), <_>::parse_v2(a)),
      (b"q", [p]) => Self::EqAssumption(<_>::parse_v2(p)),
      (b"R", [a, b, p]) => Self::Rotate(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(p)),
      (b"P", [a, b, p]) => Self::PermutePrems(<_>::parse_v2(a), <_>::parse_v2(b), <_>::parse_v2(p)),
      (b"C", [env, smax, flatten, bs, as_, a_, old_as, n, nlift, p, q]) => Self::Bicompose(
        Box::new(BicomposeArgs {
          env: <_>::parse_v2(env),
          smax: <_>::parse_v2(smax),
          flatten: <_>::parse_v2(flatten),
          bs: <_>::parse_v2(bs),
          as_: <_>::parse_v2(as_),
          a_: <_>::parse_v2(a_),
          old_as: <_>::parse_v2(old_as),
          n: <_>::parse_v2(n),
          nlift: <_>::parse_v2(nlift),
        }),
        <_>::parse_v2(p),
        <_>::parse_v2(q),
      ),
      (b"!", []) => Self::Pruned,
      _ => panic!(),
    }
  }
}

#[derive(Debug, DebugPls)]
pub struct Context {
  pub strings: IdxVec<StringId, String>,
  pub sorts: IdxVec<SortId, Sorts>,
  pub indexnames: IdxVec<IndexNameId, (StringId, u32)>,
  pub types: IdxVec<TypeId, Type>,
  pub terms: IdxVec<TermId, Term>,
  pub proofs: IdxVec<ProofId, Proof>,
  pub assumptions: IdxVec<AssumptionId, (ProofId, u32)>,
}

#[derive(Debug, DebugPls)]
pub struct Sorts(pub Vec<StringId>);
impl Parse<'_> for Sorts {
  fn parse_v2(t: &Tree<'_>) -> Self {
    Self(<_>::parse_v2(t))
  }
}

#[derive(Debug, DebugPls)]
pub struct Position {
  pub line: u32,
  pub offset: (u32, u32),
  pub label: StringId,
  pub file: StringId,
  pub id: StringId,
}
impl Parse<'_> for Position {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let [line, offset, end_offset, label, file, id] = t.as_node() else { panic!() };
    Self {
      line: <_>::parse_v2(line),
      offset: (<_>::parse_v2(offset), <_>::parse_v2(end_offset)),
      label: <_>::parse_v2(label),
      file: <_>::parse_v2(file),
      id: <_>::parse_v2(id),
    }
  }
}

#[derive(Debug, DebugPls)]
pub struct ThmName {
  pub name: StringId,
  pub i: u32,
  pub pos: Position,
}
impl Parse<'_> for ThmName {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let (name, i, pos) = <_>::parse_v2(t);
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
impl Parse<'_> for Header {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let [serial, command_pos, theory_name, thm_name, prop, types] = t.as_node() else { panic!() };
    assert!(<Option<Box<[TypeId]>>>::parse_v2(types).is_none());
    Self {
      serial: <_>::parse_v2(serial),
      command_pos: <_>::parse_v2(command_pos),
      theory_name: <_>::parse_v2(theory_name),
      thm_name: <_>::parse_v2(thm_name),
      prop: <_>::parse_v2(prop),
      // types: <_>::parse_v2(types),
    }
  }
}

#[derive(Debug, DebugPls)]
pub struct ThmTrace {
  pub ctx: Context,
  pub header: Header,
  pub root: ProofId,
  pub unconstrain_var_map: Vec<(TypeId, TypeId)>,
  pub unconstrain_shyps: u32,
  pub unconstrain_hyps: Vec<TermId>,
}
impl Parse<'_> for ThmTrace {
  fn parse_v2(t: &Tree<'_>) -> Self {
    let [strs, sorts, inames, types, terms, pfs, asms, root] = t.as_node() else { panic!() };
    let [header, uc_var_map, uc_shyps, uc_hyps, root] = root.as_node() else { panic!() };
    // println!("strings: {strings:?}");
    // println!("sorts: {sorts:?}");
    // println!("indexnames: {indexnames:?}");
    // println!("types: {types:?}");
    // println!("terms: {terms:?}");
    // println!("proofs: {proofs:?}");
    // println!("assumptions: {assumptions:?}");
    Self {
      ctx: Context {
        strings: <_>::parse_v2(strs),
        sorts: <_>::parse_v2(sorts),
        indexnames: <_>::parse_v2(inames),
        types: <_>::parse_v2(types),
        terms: <_>::parse_v2(terms),
        proofs: <_>::parse_v2(pfs),
        assumptions: <_>::parse_v2(asms),
      },
      header: <_>::parse_v2(header),
      root: <_>::parse_v2(root),
      unconstrain_var_map: <_>::parse_v2(uc_var_map),
      unconstrain_shyps: <_>::parse_v2(uc_shyps),
      unconstrain_hyps: <_>::parse_v2(uc_hyps),
    }
  }
}

impl Context {
  pub fn count_uses(&self) -> IdxVec<ProofId, u8> {
    let mut uses = IdxVec::<_, u8>::from_default(self.proofs.len());
    for pf in &self.proofs.0 {
      match *pf {
        Proof::Sorry
        | Proof::Hyp(_)
        | Proof::Axiom(_, _, _)
        | Proof::Oracle(_, _)
        | Proof::Refl(_)
        | Proof::BetaNorm(_)
        | Proof::BetaHead(_)
        | Proof::Eta(_)
        | Proof::EtaLong(_)
        | Proof::Trivial
        | Proof::OfClass(_, _)
        | Proof::Thm(_)
        | Proof::ConstrainThm(_, _)
        | Proof::Pruned => {}

        Proof::ImpIntr(_, p)
        | Proof::ForallIntr(_, p)
        | Proof::ForallElim(p, _)
        | Proof::Symm(p)
        | Proof::StripSHyps(_, p)
        | Proof::AbsRule(_, p)
        | Proof::FlexFlex(_, p)
        | Proof::Generalize(_, p)
        | Proof::Instantiate(_, p)
        | Proof::Varify(_, p)
        | Proof::LegacyFreezeT(p)
        | Proof::Lift(_, _, p)
        | Proof::IncrIndexes(_, p)
        | Proof::Rotate(_, _, p)
        | Proof::PermutePrems(_, _, p) => uses[p] = uses[p].saturating_add(1),

        Proof::ImpElim(p, q)
        | Proof::Trans(p, q)
        | Proof::AppRule(p, q)
        | Proof::EqIntr(p, q)
        | Proof::EqElim(p, q)
        | Proof::Bicompose(_, p, q) => {
          uses[p] = uses[p].saturating_add(1);
          uses[q] = uses[q].saturating_add(1);
        }

        Proof::Assumption(a, _) | Proof::EqAssumption(a) => {
          let p = self.assumptions[a].0;
          uses[p] = uses[p].saturating_add(1)
        }
      }
    }
    uses
  }
}
