use std::{
  borrow::Borrow,
  collections::{BTreeSet, HashMap, HashSet},
  hash::Hash,
};

use dbg_pls::{pretty, DebugPls};
use ref_cast::RefCast;

use crate::VerifiedThm;
use crate::{
  binparser::{BinParse, BinParser, TagPtr},
  idx::{Idx, IdxBitSet, IdxVec},
  mk_id,
  trace::{
    self, proof, AssumptionId, BicomposeArgs, ClassId, HasBinParse, IdMapping, IndexNameId, MaxIdx,
    Proof, ProofId, SortId, StringId, Subst, Table, Term, TermId, ThmTrace, TypeId,
  },
  Global,
};

/// debug hooks, all off unless the corresponding variable is set
static DEBUG_STEPS: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var_os("DEBUG_STEPS").is_some());
static DEBUG_FINAL: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var_os("DEBUG_FINAL").is_some());
static DEBUG_TRACE: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var_os("DEBUG_TRACE").is_some());
thread_local! {
  /// how often each rule was applied, for `DEBUG_RULES`
  pub static RULE_COUNTS: std::cell::RefCell<Vec<u64>> =
    std::cell::RefCell::new(vec![0; proof::END as usize]);
}
static STRICT_AS: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var_os("STRICT_AS").is_some());
static DEBUG_RULES: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var_os("DEBUG_RULES").is_some());
static DEBUG_BC: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var_os("DEBUG_BC").is_some());

mk_id! {
  HypId(u32),
  HypsId(u32),
  SortsId(u32),
  TpairsId(u32),
  LCtxId(u32),
}

impl TpairsId {
  const EMPTY: Self = Self(0);
}

type Lookup<I, T, D> = (IdxVec<I, (T, D)>, HashMap<T, I>);

#[derive(Hash, PartialEq, Eq, RefCast)]
#[repr(transparent)]
struct Wrap<T>(T);
trait TempKey<'a, K>: Hash + Eq + Sized {
  fn upgrade(&self, ck: &Checker<'a>) -> K;
}

#[derive(Clone, Debug, DebugPls, Hash, PartialEq, Eq)]
pub enum LCtx {
  Nil,
  Cons(LCtxId, TypeId),
}

#[derive(Clone, Debug, DebugPls, Hash, PartialEq, Eq)]
pub enum Type<'a> {
  Type(StringId, &'a [TypeId]),
  Free(StringId, SortId),
  Var(IndexNameId, SortId),
}
impl<'a> BinParse<'_, BM<'a, '_>> for Type<'a> {
  fn parse(ctx: &mut BM<'a, '_>, bp: &BinParser<'_>, p: TagPtr) -> Self {
    match bp.get_enum(p) {
      (0, &[x, s]) => Self::Free(bp.parse(ctx, x), bp.parse(ctx, s)),
      (1, &[i, s]) => Self::Var(bp.parse(ctx, i), bp.parse(ctx, s)),
      (2, &[s, tys]) => Self::Type(bp.parse(ctx, s), bp.parse(ctx, tys)),
      _ => panic!(),
    }
  }
}
impl<'a, 'b, 'c, T: BinParse<'c, BM<'a, 'b>>> BinParse<'c, BM<'a, 'b>> for &'a [T] {
  fn parse(ctx: &mut BM<'a, 'b>, bp: &BinParser<'c>, p: TagPtr) -> Self {
    ctx.0.alloc.alloc_slice_fill_iter(bp.parse_list(p).map(|a| bp.parse(ctx, a)))
  }
}

impl<'a> Type<'a> {
  pub fn as_type(&self) -> (StringId, &'a [TypeId]) {
    let Type::Type(s, vec) = *self else { panic!("expected type constructor") };
    (s, vec)
  }
  pub fn as_fun(&self) -> (TypeId, TypeId) {
    let (StringId::FUN, &[a, b]) = self.as_type() else { panic!("expected function type") };
    (a, b)
  }
}
impl<'a: 'b, 'b> Borrow<Wrap<Type<'b>>> for Type<'a> {
  fn borrow(&self) -> &Wrap<Type<'b>> {
    Wrap::ref_cast(self)
  }
}
impl<'a: 'b, 'b> TempKey<'a, Type<'a>> for Type<'b> {
  fn upgrade(&self, ck: &Checker<'a>) -> Type<'a> {
    match *self {
      Type::Type(c, ts) => Type::Type(c, ck.alloc.alloc_slice_copy(ts)),
      Type::Free(v, s) => Type::Free(v, s),
      Type::Var(n, s) => Type::Var(n, s),
    }
  }
}
impl<'a: 'b, 'b, T> Borrow<Wrap<&'b [T]>> for &'a [T] {
  fn borrow(&self) -> &Wrap<&'b [T]> {
    Wrap::ref_cast(self)
  }
}
impl<'a: 'b, 'b, T: Hash + Eq + Copy> TempKey<'a, &'a [T]> for &'b [T] {
  fn upgrade(&self, ck: &Checker<'a>) -> &'a [T] {
    ck.alloc.alloc_slice_copy(self)
  }
}

impl<'a: 'b, 'b> Borrow<Wrap<&'b str>> for &'a str {
  fn borrow(&self) -> &Wrap<&'b str> {
    Wrap::ref_cast(self)
  }
}
impl<'a: 'b, 'b> TempKey<'a, &'a str> for &'b str {
  fn upgrade(&self, ck: &Checker<'a>) -> &'a str {
    ck.alloc.alloc_str(self)
  }
}

#[derive(Debug, DebugPls, Clone, Hash, PartialEq, Eq)]
struct CProof {
  shyps: SortsId,
  hyps: HypsId,
  /// the flex-flex pairs the theorem still carries (`Thm.tpairs_of`), discharged by
  /// `FlexFlex` and forbidden in a stored theorem
  tpairs: TpairsId,
  concl: TermId,
}

macro_rules! mk_checker_ctx {
  (@data) => {
    fn mk_data(_: &mut Checker<'_>, _: &Self::Key) -> Self::Data { Default::default() }
  };
  (@data |$cc:ident, $k:ident| $e:expr) => {
    fn mk_data($cc: &mut Checker<'_>, $k: &Self::Key) -> Self::Data { $e }
  };
  (struct CheckerCtx<$a:lifetime> {
    $($field:ident: $id:ty => ($tty:ty, $cty:ty, $d:ty) $(reg $($reg:literal)?)? $((data $($data:tt)*))?,)*
  }) => {
    #[derive(Debug, DebugPls, Default)]
    struct CheckerCtx<$a> {
      $($field: Lookup<$id, $cty, $d>,)*
    }
    #[derive(Default)]
    struct Mapping {
      $($($field: HashMap<TagPtr, $id>, $($reg)?)?)*
    }
    $(
      impl<$a> HasAccessors<CheckerCtx<$a>> for $id {
        type Val = ($cty, $d);
        fn get<'b>(m: &'b CheckerCtx<$a>) -> &'b IdxVec<Self, Self::Val> { &m.$field.0 }
        fn get_mut<'b>(m: &'b mut CheckerCtx<$a>) -> &'b mut IdxVec<Self, Self::Val> { &mut m.$field.0 }
      }
      impl<$a> HasAlloc<$a> for $id {
        type Key = $cty;
        type Data = $d;
        fn get_alloc<'b>(m: &'b mut CheckerCtx<$a>) -> &'b mut Lookup<Self, Self::Key, Self::Data> {
          &mut m.$field
        }
        mk_checker_ctx! { @data $($($data)*)? }
      }
      impl<$a> std::ops::Index<$id> for CheckerCtx<$a> {
        type Output = ($cty, $d);
        fn index(&self, i: $id) -> &Self::Output { &self.$field.0[i] }
      }
      $(
        impl HasMapping for $id {
          fn get(m: &Mapping) -> &HashMap<TagPtr, $id> { &m.$field }
          fn get_mut(m: &mut Mapping) -> &mut HashMap<TagPtr, $id> { &mut m.$field }
        }
      $($reg)?)?
    )*
  };
}
mk_checker_ctx! {
  struct CheckerCtx<'a> {
    strings: StringId => (String, &'a str, ()) reg,
    sorts: SortId => (trace::Sorts, IdxBitSet<ClassId>, ()) reg,
    indexnames: IndexNameId => ((StringId, u32), (StringId, u32), ()) reg,
    types: TypeId => (trace::Type, Type<'a>, TypeData) reg
      (data |ck, k| TypeData::mk(ck, k)),
    terms: TermId => (Term, Term, TermData) reg (data |ck, k| TermData::mk(ck, k)),
    proofs: ProofId => (Proof, CProof, ()) reg,
    assumptions: AssumptionId => ((ProofId, u32), (ProofId, u32), ()) reg,
    hyps: HypId => ((), TermId, ())
      (data |ck, k| ck.check_hyp(*k)),
    classes: ClassId => (StringId, StringId, ()) reg,
    hypss: HypsId => ((), IdxBitSet<HypId>, ()),
    tpairss: TpairsId => ((), Box<[(TermId, TermId)]>, ()),
    sortss: SortsId => ((), IdxBitSet<SortId>, ()),
    lctxs: LCtxId => ((), LCtx, ()),
  }
}

type BM<'a, 'b> = (&'b mut Checker<'a>, &'b mut Mapping);
impl<'a, 'b> IdMapping for BM<'a, 'b> {}

impl<'a> BinParse<'_, BM<'a, '_>> for &'a str {
  fn parse(ctx: &mut BM<'a, '_>, bp: &BinParser<'_>, p: TagPtr) -> Self {
    ctx.0.alloc.alloc_str(std::str::from_utf8(bp.get(p.as_ptr()).as_str()).unwrap())
  }
}

impl<'a> BinParse<'_, BM<'a, '_>> for IdxBitSet<ClassId> {
  fn parse(ctx: &mut BM<'a, '_>, bp: &BinParser<'_>, p: TagPtr) -> Self {
    let mut out = IdxBitSet::new();
    for a in bp.parse_list(p) {
      out.insert(bp.parse(ctx, a));
    }
    out
  }
}

trait HasMapping: Idx {
  fn get(_: &Mapping) -> &HashMap<TagPtr, Self>;
  fn get_mut(_: &mut Mapping) -> &mut HashMap<TagPtr, Self>;
}
trait HasAccessors<T>: Idx {
  type Val;
  fn get(_: &T) -> &IdxVec<Self, Self::Val>;
  fn get_mut(_: &mut T) -> &mut IdxVec<Self, Self::Val>;
}
trait HasAlloc<'a>: HasAccessors<CheckerCtx<'a>, Val = (Self::Key, Self::Data)> {
  type Key: Clone + Hash + Eq + std::fmt::Debug;
  type Data;
  fn get_alloc<'b>(cc: &'b mut CheckerCtx<'a>) -> &'b mut Lookup<Self, Self::Key, Self::Data>;
  fn mk_data(ck: &mut Checker<'a>, k: &Self::Key) -> Self::Data;
}

impl<'a, 'b, I> HasBinParse<I> for BM<'a, 'b>
where
  I: HasMapping + HasAlloc<'a> + 'a,
  for<'c> <I as HasAlloc<'a>>::Key: BinParse<'c, BM<'a, 'b>>,
{
  fn parse(&mut self, bp: &BinParser<'_>, p: TagPtr) -> I {
    match HasMapping::get(self.1).get(&p) {
      Some(&i) => i,
      None => {
        let val = BinParse::parse(self, bp, p);
        let i = self.0.alloc(val);
        HasMapping::get_mut(self.1).insert(p, i);
        i
      }
    }
  }
}

trait BitSetIdx<'a>: HasAlloc<'a, Key = IdxBitSet<Self::Elem>> {
  const EMPTY: Self;
  type Elem: Idx;
}

trait Treeify {
  type Output;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output;
}
impl<A: Treeify, B: Treeify> Treeify for (A, B) {
  type Output = (A::Output, B::Output);
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    (self.0.treeify(ctx), self.1.treeify(ctx))
  }
}
impl<A: Treeify, B: Treeify, C: Treeify> Treeify for (A, B, C) {
  type Output = (A::Output, B::Output, C::Output);
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    (self.0.treeify(ctx), self.1.treeify(ctx), self.2.treeify(ctx))
  }
}
impl<T: Treeify> Treeify for [T] {
  type Output = Vec<T::Output>;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    self.iter().map(|i| i.treeify(ctx)).collect()
  }
}
impl<T: Treeify> Treeify for Vec<T> {
  type Output = Vec<T::Output>;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    (**self).treeify(ctx)
  }
}
impl<I: Treeify + Idx> Treeify for IdxBitSet<I> {
  type Output = Vec<I::Output>;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    self.iter().map(|i| i.treeify(ctx)).collect()
  }
}
impl Treeify for StringId {
  type Output = String;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    ctx[*self].0.to_owned()
  }
}
impl Treeify for ClassId {
  type Output = crate::Class;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    ctx[*self].0.treeify(ctx)
  }
}
impl Treeify for SortId {
  type Output = crate::Sort;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    ctx[*self].0.treeify(ctx)
  }
}
impl Treeify for SortsId {
  type Output = Vec<crate::Sort>;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    ctx[*self].0.treeify(ctx)
  }
}
impl Treeify for IndexNameId {
  type Output = (String, u32);
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    let (s, i) = ctx[*self].0;
    (s.treeify(ctx), i)
  }
}
impl Treeify for TypeId {
  type Output = crate::Type;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    match &ctx[*self].0 {
      Type::Type(s, ty) => crate::Type::Type(s.treeify(ctx), ty.treeify(ctx)),
      Type::Free(s, so) => crate::Type::Free(s.treeify(ctx), so.treeify(ctx)),
      Type::Var(n, so) => {
        let (s, i) = n.treeify(ctx);
        crate::Type::Var(s, i, so.treeify(ctx))
      }
    }
  }
}
impl Treeify for TermId {
  type Output = crate::Term;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    match ctx[*self].0 {
      Term::Const(s, ty) => crate::Term::Const2(s.treeify(ctx), Box::new(ty.treeify(ctx))),
      Term::Free(s, ty) => crate::Term::Free(s.treeify(ctx), Some(Box::new(ty.treeify(ctx)))),
      Term::Var(n, ty) => {
        let (s, i) = n.treeify(ctx);
        crate::Term::Var(s, i, Some(Box::new(ty.treeify(ctx))))
      }
      Term::Bound(i) => crate::Term::Bound(i),
      Term::Abs(x, ty, e) => {
        crate::Term::Abs(x.treeify(ctx), Box::new(ty.treeify(ctx)), Box::new(e.treeify(ctx)))
      }
      Term::App(e1, e2) => crate::Term::App(Box::new(e1.treeify(ctx)), Box::new(e2.treeify(ctx))),
    }
  }
}
impl Treeify for HypId {
  type Output = crate::Term;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    ctx[*self].0.treeify(ctx)
  }
}
impl Treeify for HypsId {
  type Output = Vec<crate::Term>;
  fn treeify(&self, ctx: &CheckerCtx<'_>) -> Self::Output {
    ctx[*self].0.treeify(ctx)
  }
}

#[derive(Debug, DebugPls, Clone)]
struct TypeData {
  sorts: SortsId,
  maxidx: MaxIdx,
}
impl TypeData {
  fn mk(ck: &mut Checker<'_>, t: &Type) -> TypeData {
    match *t {
      Type::Type(c, ts) => match ts {
        [] => {
          ck.check_type_decl(c, ts);
          TypeData { sorts: SortsId::EMPTY, maxidx: MaxIdx::NONE }
        }
        &[t] => {
          ck.check_type_decl(c, ts);
          ck.ctx[t].1.clone()
        }
        _ => {
          ck.check_type_decl(c, ts);
          let mut sorts = IdxBitSet::new();
          let maxidx = MaxIdx::fold_max(ts.iter().map(|&t| {
            let data = &ck.ctx[t].1;
            sorts.union_with(&ck.ctx[data.sorts].0);
            data.maxidx
          }));
          TypeData { sorts: ck.alloc(sorts), maxidx }
        }
      },
      Type::Free(_, s) => TypeData { sorts: ck.alloc(IdxBitSet::single(s)), maxidx: MaxIdx::NONE },
      Type::Var(i, s) => {
        TypeData { sorts: ck.alloc(IdxBitSet::single(s)), maxidx: MaxIdx::var(ck.ctx[i].0 .1) }
      }
    }
  }
}

#[derive(Debug, DebugPls)]
struct TermData {
  sorts: SortsId,
  maxidx: MaxIdx,
  /// if Err(i), then the largest Bound var blocking the type is i; `UNKNOWN_TY` means the
  /// head of an application has no function type yet (an uninstantiated type variable), so
  /// the type is only determined once a substitution has been applied
  ty: Result<TypeId, u32>,
}

/// see [`TermData::ty`]
const UNKNOWN_TY: u32 = u32::MAX;

impl TermData {
  fn mk(ck: &mut Checker<'_>, t: &Term) -> TermData {
    match *t {
      Term::Const(c, ty) => {
        ck.check_const_decl(c, ty);
        let data = &ck.ctx[ty].1;
        TermData { sorts: data.sorts, maxidx: data.maxidx, ty: Ok(ty) }
      }
      Term::Free(_, ty) => {
        let data = &ck.ctx[ty].1;
        TermData { sorts: data.sorts, maxidx: data.maxidx, ty: Ok(ty) }
      }
      Term::Var(i, ty) => {
        TermData { sorts: ck.ctx[ty].1.sorts, maxidx: MaxIdx::var(ck.ctx[i].0 .1), ty: Ok(ty) }
      }
      Term::Bound(i) => TermData { sorts: SortsId::EMPTY, maxidx: MaxIdx::NONE, ty: Err(i) },
      Term::Abs(_, dom, e) => {
        let TypeData { sorts: ds, maxidx: dm } = ck.ctx[dom].1;
        let TermData { sorts: es, maxidx: em, ty } = ck.ctx[e].1;
        let maxidx = dm.max(em);
        let sorts = ck.union(ds, es);
        let ty = match ty {
          Ok(rng) => Ok(ck.mk_fun(dom, rng)),
          // the body's type is only determined under the binder; the lambda's type is
          // still `dom -> body`, not the body's type
          Err(0) => {
            let lctx = ck.mk_lctx(LCtxId::NIL, dom);
            // a term recorded inside an `Envir` is only well-typed *modulo* the type
            // environment -- an application's head can have a type variable for a type --
            // so a type that cannot be computed is unknown rather than an error
            match ck.try_get_type_ctx(lctx, e) {
              Some(rng) => Ok(ck.mk_fun(dom, rng)),
              None => Err(UNKNOWN_TY),
            }
          }
          Err(i) => Err(i - 1),
        };
        TermData { sorts, maxidx, ty }
      }
      Term::App(e1, e2) => {
        let TermData { sorts: s1, maxidx: m1, ty: ty1 } = ck.ctx[e1].1;
        let TermData { sorts: s2, maxidx: m2, ty: _ } = ck.ctx[e2].1;
        let ty = match ty1 {
          Ok(ty) => match ck.ctx[ty].0 {
            Type::Type(StringId::FUN, &[_, rng]) => Ok(rng),
            _ => Err(UNKNOWN_TY),
          },
          e => e,
        };
        let sorts = ck.union(s1, s2);
        TermData { sorts, maxidx: m1.max(m2), ty }
      }
    }
  }
}

#[derive(Clone, Copy)]
struct OfClassCache {
  itself: StringId,
  type_: StringId,
}

pub struct Checker<'a> {
  ctx: CheckerCtx<'a>,
  type_cache: HashMap<(LCtxId, TermId), TypeId>,
  imp: Option<TermId>,
  ofclass_cache: Option<OfClassCache>,
  cited_cache: HashMap<u32, TermId>,
  class_supers: HashMap<ClassId, IdxBitSet<ClassId>>,
  sort_closure: HashMap<SortId, IdxBitSet<ClassId>>,
  arity_cache: HashMap<(StringId, ClassId), Option<Vec<IdxBitSet<ClassId>>>>,
  of_sort_cache: HashMap<(TypeId, SortId), bool>,
  eta_long_cache: HashMap<(LCtxId, TermId), TermId>,
  axiom_sorts: HashMap<String, Vec<String>>,
  type_decl_cache: HashSet<StringId>,
  const_decl_cache: HashSet<(StringId, TypeId)>,
  alloc: &'a bumpalo::Bump,
  g: &'a Global,
}

impl StringId {
  const FUN: Self = Self(0);
  const PROP: Self = Self(1);
  // interned up front by `Checker::new`, so the destructors below compare ids, not strings
  const EQ: Self = Self(2);
  const IMP: Self = Self(3);
  const ALL: Self = Self(4);
}
impl BitSetIdx<'_> for HypsId {
  const EMPTY: Self = Self(0);
  type Elem = HypId;
}
impl SortId {
  const TOP: Self = Self(0);
}
impl BitSetIdx<'_> for SortsId {
  const EMPTY: Self = Self(0);
  type Elem = SortId;
}
impl LCtxId {
  const NIL: Self = Self(0);
}
impl TypeId {
  const PROP: Self = Self(0);
}

impl<'a> Checker<'a> {
  pub fn new(alloc: &'a bumpalo::Bump, g: &'a Global) -> Self {
    let mut ck = Checker {
      ctx: CheckerCtx::default(),
      alloc,
      g,
      type_cache: Default::default(),
      cited_cache: Default::default(),
      class_supers: Default::default(),
      sort_closure: Default::default(),
      arity_cache: Default::default(),
      of_sort_cache: Default::default(),
      eta_long_cache: Default::default(),
      axiom_sorts: Default::default(),
      type_decl_cache: Default::default(),
      const_decl_cache: Default::default(),
      ofclass_cache: None,
      imp: None,
    };
    ck.alloc::<StringId>("fun");
    ck.alloc::<StringId>("prop");
    ck.alloc::<StringId>("Pure.eq");
    ck.alloc::<StringId>("Pure.imp");
    ck.alloc::<StringId>("Pure.all");
    ck.alloc::<HypsId>(IdxBitSet::new());
    ck.alloc::<TpairsId>(Box::new([]));
    ck.alloc::<SortId>(IdxBitSet::new());
    ck.alloc::<SortsId>(IdxBitSet::new());
    ck.alloc::<LCtxId>(LCtx::Nil);
    ck.alloc::<TypeId>(Type::Type(StringId::PROP, &[]));
    ck
  }

  fn pp<T: Treeify>(&self, t: T) -> T::Output {
    t.treeify(&self.ctx)
  }

  fn alloc<I: HasAlloc<'a>>(&mut self, k: I::Key) -> I {
    if let Some(&i) = I::get_alloc(&mut self.ctx).1.get(&k) {
      i
    } else {
      let v = I::mk_data(self, &k);
      let a = I::get_alloc(&mut self.ctx);
      let i = a.0.push((k.clone(), v));
      // println!("alloc {} {i:?} = {k:?}", std::any::type_name::<I>());
      a.1.insert(k, i);
      i
    }
  }

  fn alloc_copy<I: HasAlloc<'a>, Q: TempKey<'a, I::Key>>(&mut self, k: &Q) -> I
  where
    I::Key: Borrow<Wrap<Q>>,
  {
    if let Some(&i) = I::get_alloc(&mut self.ctx).1.get(Wrap::ref_cast(k)) {
      i
    } else {
      let k = k.upgrade(self);
      let v = I::mk_data(self, &k);
      let a = I::get_alloc(&mut self.ctx);
      let i = a.0.push((k.clone(), v));
      a.1.insert(k, i);
      i
    }
  }

  fn mk_fun(&mut self, a: TypeId, b: TypeId) -> TypeId {
    self.alloc_copy(&Type::Type(StringId::FUN, &[a, b]))
  }

  fn try_dest_fun(&self, a: TypeId) -> Option<(TypeId, TypeId)> {
    let Type::Type(StringId::FUN, &[a, b]) = self.ctx[a].0 else { return None };
    Some((a, b))
  }

  fn dest_fun(&self, a: TypeId) -> (TypeId, TypeId) {
    self.try_dest_fun(a).expect("expected function")
  }

  fn mk_lctx(&mut self, lctx: LCtxId, ty: TypeId) -> LCtxId {
    self.alloc(LCtx::Cons(lctx, ty))
  }

  fn try_dest_app(&self, a: TermId) -> Option<(TermId, TermId)> {
    let Term::App(e1, e2) = self.ctx[a].0 else { return None };
    Some((e1, e2))
  }

  fn dest_app(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_app(a).expect("expected application")
  }

  fn try_dest_const(&self, a: TermId) -> Option<(StringId, TypeId)> {
    let Term::Const(s, ty) = self.ctx[a].0 else { return None };
    Some((s, ty))
  }

  fn dest_const(&self, a: TermId) -> (StringId, TypeId) {
    self.try_dest_const(a).expect("expected constant")
  }

  fn dest_type<const N: usize>(&self, a: TypeId) -> (StringId, &'a [TypeId; N]) {
    let Type::Type(s, ty) = self.ctx[a].0 else { panic!("expected type constant") };
    (s, ty.try_into().expect("incorrect number of arguments"))
  }

  fn dest_tvar(&self, a: TypeId) -> (IndexNameId, SortId) {
    let Type::Var(x, s) = self.ctx[a].0 else { panic!("expected type variable") };
    (x, s)
  }

  fn try_dest_imp(&self, a: TermId) -> Option<(TermId, TermId)> {
    let (f, e2) = self.try_dest_app(a)?;
    let (f, e1) = self.try_dest_app(f)?;
    let (c, _) = self.try_dest_const(f)?;
    if c != StringId::IMP {
      return None;
    }
    Some((e1, e2))
  }

  fn dest_imp(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_imp(a).expect("expected implication")
  }
  fn mk_imp_term(&mut self) -> TermId {
    self.imp.unwrap_or_else(|| {
      let ty = self.mk_fun(TypeId::PROP, TypeId::PROP);
      let ty = self.mk_fun(TypeId::PROP, ty);
      let imp = self.alloc(Term::Const(StringId::IMP, ty));
      *self.imp.insert(imp)
    })
  }

  fn mk_imp(&mut self, a: TermId, b: TermId) -> TermId {
    let f = self.mk_imp_term();
    let f = self.alloc(Term::App(f, a));
    self.alloc(Term::App(f, b))
  }

  fn mk_forall(&mut self, x: StringId, ty: TypeId, body: TermId) -> TermId {
    let pred = self.mk_fun(ty, TypeId::PROP);
    let cty = self.mk_fun(pred, TypeId::PROP);
    let all = self.alloc(Term::Const(StringId::ALL, cty));
    let abs = self.alloc(Term::Abs(x, ty, body));
    self.alloc(Term::App(all, abs))
  }

  /// `Term.strip_all_vars` / `Term.strip_all_body`: the leading `⋀`-parameters and the
  /// body underneath them
  fn strip_all(&self, mut a: TermId, out: &mut Vec<(StringId, TypeId)>) -> TermId {
    while let Some((_, e)) = self.try_dest_forall(a) {
      let Term::Abs(x, ty, t) = self.ctx[e].0 else { break };
      out.push((x, ty));
      a = t
    }
    a
  }

  /// A unifier assigns `?'a::S := T` only when `T` is of sort `S` (`Type.unify` meets the
  /// sorts as it goes); the trace hands us the finished environment, so check it.  The
  /// `tyenv` need not be idempotent, hence the normalised right-hand side.
  fn check_env_sorts(&mut self, inst: &mut Mapper<TermId, InstTerm>) {
    for &(_, s, ty) in &inst.f.ty.f.subst.clone() {
      let ty = inst.f.ty.apply(self, ty);
      if !self.of_sort(ty, s) {
        println!("!! unifier: {:?} not of sort {:?}", self.pp(ty), self.pp(s));
      }
      assert!(self.of_sort(ty, s), "unifier: type not of sort");
    }
  }

  /// Bring a proposition from the theory export into this checker.  The export encodes a
  /// constant by its *type arguments*, so the type is rebuilt from the declaration.
  fn reify_axiom(&mut self, t: &crate::Term) -> TermId {
    match t {
      crate::Term::Const(c, tyargs) => {
        let (typargs, decl) = (self.g.consts.get(c))
          .unwrap_or_else(|| panic!("axiom mentions undeclared constant {c}"))
          .clone();
        let tys: Vec<TypeId> = tyargs.iter().map(|t| self.reify_decl_type(t, &[])).collect();
        let subst: HashMap<String, TypeId> =
          typargs.iter().cloned().zip(tys).collect();
        let ty = self.reify_decl_type(&decl, &subst.iter().map(|(a, b)| (a.clone(), *b)).collect::<Vec<_>>());
        let c = self.alloc_copy(&&**c);
        self.alloc(Term::Const(c, ty))
      }
      crate::Term::Const2(c, ty) => {
        let ty = self.reify_decl_type(ty, &[]);
        let c = self.alloc_copy(&&**c);
        self.alloc(Term::Const(c, ty))
      }
      crate::Term::Free(x, Some(ty)) => {
        let ty = self.reify_decl_type(ty, &[]);
        let x = self.alloc_copy(&&**x);
        self.alloc(Term::Free(x, ty))
      }
      crate::Term::Var(x, i, Some(ty)) => {
        let ty = self.reify_decl_type(ty, &[]);
        let x = self.alloc_copy(&&**x);
        let x = self.alloc((x, *i));
        self.alloc(Term::Var(x, ty))
      }
      crate::Term::Bound(i) => self.alloc(Term::Bound(*i)),
      crate::Term::Abs(x, ty, e) => {
        let ty = self.reify_decl_type(ty, &[]);
        let e = self.reify_axiom(e);
        let x = self.alloc_copy(&&**x);
        self.alloc(Term::Abs(x, ty, e))
      }
      crate::Term::App(f, u) => {
        let f = self.reify_axiom(f);
        let u = self.reify_axiom(u);
        self.alloc(Term::App(f, u))
      }
      // `OFCLASS(T, c)` is `c_class (TYPE(T))`
      crate::Term::OfClass(c, ty) => {
        let ty = self.reify_decl_type(ty, &[]);
        let itself = self.alloc("itself");
        let type_ = self.alloc("Pure.type");
        let cname = self.alloc_copy(&&*format!("{c}_class"));
        let itself_t = self.alloc_copy(&Type::Type(itself, &[ty]));
        let cty = self.mk_fun(itself_t, TypeId::PROP);
        let f = self.alloc(Term::Const(cname, cty));
        let a = self.alloc(Term::Const(type_, itself_t));
        self.alloc(Term::App(f, a))
      }
      _ => panic!("axiom: unexpected term shape"),
    }
  }

  fn reify_decl_type(&mut self, ty: &crate::Type, subst: &[(String, TypeId)]) -> TypeId {
    match ty {
      crate::Type::Type(c, args) => {
        let args: Vec<TypeId> = args.iter().map(|a| self.reify_decl_type(a, subst)).collect();
        let c = self.alloc_copy(&&**c);
        self.alloc_copy(&Type::Type(c, &args))
      }
      crate::Type::Free(x, s) => match subst.iter().find(|(y, _)| y == x) {
        Some(&(_, t)) => t,
        None => {
          let s = self.axiom_sort(x, s);
          let s = self.reify_sort_names(&s);
          let x = self.alloc_copy(&&**x);
          self.alloc(Type::Free(x, s))
        }
      },
      crate::Type::Var(x, i, s) => match subst.iter().find(|(y, _)| y == x) {
        Some(&(_, t)) => t,
        None => {
          let s = self.axiom_sort(x, s);
          let s = self.reify_sort_names(&s);
          let x = self.alloc_copy(&&**x);
          let x = self.alloc((x, *i));
          self.alloc(Type::Var(x, s))
        }
      },
    }
  }

  /// Rename every schematic variable to a canonical name, in order of first occurrence, so
  /// that two statements can be compared for equality despite the export's `standard_prop`
  /// having renamed them.
  fn canon_stmt(&mut self, t: TermId) -> TermId {
    let mut tm = HashMap::new();
    let mut ty = HashMap::new();
    self.canon_term(t, &mut tm, &mut ty)
  }

  fn canon_term(
    &mut self, t: TermId, tm: &mut HashMap<IndexNameId, IndexNameId>,
    ty: &mut HashMap<IndexNameId, IndexNameId>,
  ) -> TermId {
    match self.ctx[t].0 {
      Term::Const(c, t1) => {
        let t1 = self.canon_type(t1, ty);
        self.alloc(Term::Const(c, t1))
      }
      // `standard_prop` writes the variables of an exported statement as `Free`s where the
      // stored axiom has `Var`s, so both go into the same canonical namespace
      Term::Free(x, t1) => {
        let t1 = self.canon_type(t1, ty);
        let x = self.alloc((x, 0));
        let x = match tm.get(&x) {
          Some(&y) => y,
          None => {
            let n = self.alloc_copy(&&*format!("v{}", tm.len()));
            let y = self.alloc((n, 0));
            tm.insert(x, y);
            y
          }
        };
        self.alloc(Term::Var(x, t1))
      }
      Term::Var(x, t1) => {
        let t1 = self.canon_type(t1, ty);
        let x = match tm.get(&x) {
          Some(&y) => y,
          None => {
            let n = self.alloc_copy(&&*format!("v{}", tm.len()));
            let y = self.alloc((n, 0));
            tm.insert(x, y);
            y
          }
        };
        self.alloc(Term::Var(x, t1))
      }
      Term::Bound(i) => self.alloc(Term::Bound(i)),
      // binder names are irrelevant, and `standard_prop` renames them to avoid clashing
      // with the variables it introduces
      Term::Abs(_, t1, e) => {
        let t1 = self.canon_type(t1, ty);
        let e = self.canon_term(e, tm, ty);
        let x = self.alloc("_");
        self.alloc(Term::Abs(x, t1, e))
      }
      Term::App(f, u) => {
        let f = self.canon_term(f, tm, ty);
        let u = self.canon_term(u, tm, ty);
        self.alloc(Term::App(f, u))
      }
    }
  }

  fn canon_type(&mut self, t: TypeId, ty: &mut HashMap<IndexNameId, IndexNameId>) -> TypeId {
    match self.ctx[t].0 {
      Type::Type(c, args) => {
        let args: Vec<TypeId> =
          args.to_vec().into_iter().map(|a| self.canon_type(a, ty)).collect();
        self.alloc_copy(&Type::Type(c, &args))
      }
      Type::Free(x, s) => {
        let x = self.alloc((x, 0));
        let x = match ty.get(&x) {
          Some(&y) => y,
          None => {
            let n = self.alloc_copy(&&*format!("'t{}", ty.len()));
            let y = self.alloc((n, 0));
            ty.insert(x, y);
            y
          }
        };
        self.alloc(Type::Var(x, s))
      }
      Type::Var(x, s) => {
        let x = match ty.get(&x) {
          Some(&y) => y,
          None => {
            let n = self.alloc_copy(&&*format!("'t{}", ty.len()));
            let y = self.alloc((n, 0));
            ty.insert(x, y);
            y
          }
        };
        self.alloc(Type::Var(x, s))
      }
    }
  }

  /// `Sign.certify_term`'s declaration checks, one per interned id: a type constructor is
  /// applied to exactly its declared arity, and a constant's type is an instance of the
  /// type it was declared with -- whose type variables carry sorts the instance has to
  /// satisfy.  Without this a trace could use a constant at a type it was never given.
  fn check_type_decl(&mut self, c: StringId, args: &[TypeId]) {
    if self.type_decl_cache.contains(&c) {
      return
    }
    let name = self.ctx.strings.0[c].0.to_string();
    match self.g.types.get(&name) {
      Some(&n) => assert!(n == args.len(), "type constructor {name} applied to {} arguments, \
        but declared with {n}", args.len()),
      // `fun` and `prop` are built in rather than declared
      None => assert!(
        name == "fun" || name == "prop" || name == "itself" || name == "dummy",
        "undeclared type constructor {name}"
      ),
    }
    self.type_decl_cache.insert(c);
  }

  fn check_const_decl(&mut self, c: StringId, ty: TypeId) {
    if self.const_decl_cache.contains(&(c, ty)) {
      return
    }
    let name = self.ctx.strings.0[c].0.to_string();
    if let Some((typargs, decl)) = self.g.consts.get(&name) {
      let (typargs, decl) = (typargs.clone(), decl.clone());
      // first-order matching of the declared type against the occurrence
      let mut subst: HashMap<String, TypeId> = HashMap::new();
      assert!(
        self.match_decl_type(&decl, ty, &typargs, &mut subst),
        "constant {name} used at a type that is not an instance of its declaration"
      );
      // the declared type variables carry sorts, which the instance must satisfy
      for (x, t) in subst {
        if let Some(sort) = decl_var_sort(&decl, &x) {
          let s = self.reify_sort_names(&sort);
          assert!(self.of_sort(t, s), "constant {name}: type argument not of sort");
        }
      }
    }
    self.const_decl_cache.insert((c, ty));
  }

  /// match a declared type (whose variables are the constant's type arguments) against an
  /// occurrence
  fn match_decl_type(
    &mut self, decl: &crate::Type, ty: TypeId, typargs: &[String], subst: &mut HashMap<String, TypeId>,
  ) -> bool {
    match decl {
      crate::Type::Free(x, _) | crate::Type::Var(x, _, _) if typargs.contains(x) => {
        match subst.get(x) {
          Some(&t) => t == ty,
          None => {
            subst.insert(x.clone(), ty);
            true
          }
        }
      }
      crate::Type::Free(x, _) => matches!(self.ctx[ty].0, Type::Free(y, _)
        if self.ctx.strings.0[y].0 == x),
      crate::Type::Var(x, i, _) => matches!(self.ctx[ty].0, Type::Var(y, _)
        if self.ctx.strings.0[self.ctx[y].0 .0].0 == x && self.ctx[y].0 .1 == *i),
      crate::Type::Type(c, args) => match self.ctx[ty].0 {
        Type::Type(c2, args2) => {
          self.ctx.strings.0[c2].0 == c
            && args.len() == args2.len()
            && (args.iter().zip(args2.to_vec()))
              .all(|(a, b)| self.match_decl_type(a, b, typargs, subst))
        }
        _ => false,
      },
    }
  }

  /// the sort `standard_prop` moved out of the statement into its `typargs`
  fn axiom_sort(&self, x: &str, s: &[String]) -> Vec<String> {
    if s.is_empty() {
      self.axiom_sorts.get(x).cloned().unwrap_or_default()
    } else {
      s.to_vec()
    }
  }

  fn reify_sort_names(&mut self, s: &[String]) -> SortId {
    let mut bits = IdxBitSet::new();
    for c in s {
      let c = self.alloc_copy(&&**c);
      let c: ClassId = self.alloc(c);
      bits.insert(c);
    }
    self.alloc(bits)
  }

  /// The class algebra, interned into this checker's ids on first use: the global one is
  /// keyed by strings, and looking a type up in it per node made the sort checks cost more
  /// than everything else put together.
  fn class_supers(&mut self, c: ClassId) -> IdxBitSet<ClassId> {
    if let Some(s) = self.class_supers.get(&c) {
      return s.clone()
    }
    let name = self.ctx.strings.0[self.ctx[c].0].0.to_string();
    let mut set = IdxBitSet::new();
    set.insert(c);
    if let Some(sup) = self.g.classes.supers.get(&name) {
      for d in sup.clone() {
        let d = self.alloc_copy(&&*d);
        let d: ClassId = self.alloc(d);
        set.insert(d);
      }
    }
    self.class_supers.insert(c, set.clone());
    set
  }

  /// everything a sort entails
  fn sort_closure(&mut self, s: SortId) -> IdxBitSet<ClassId> {
    if let Some(s) = self.sort_closure.get(&s) {
      return s.clone()
    }
    let mut out = IdxBitSet::new();
    for c in self.ctx[s].0.clone().iter() {
      out.union_with(&self.class_supers(c));
    }
    self.sort_closure.insert(s, out.clone());
    out
  }

  /// the argument sorts an arity requires, as class sets
  fn arity(&mut self, a: StringId, c: ClassId) -> Option<Vec<IdxBitSet<ClassId>>> {
    if let Some(x) = self.arity_cache.get(&(a, c)) {
      return x.clone()
    }
    let key = (
      self.ctx.strings.0[a].0.to_string(),
      self.ctx.strings.0[self.ctx[c].0].0.to_string(),
    );
    let val = self.g.classes.arities.get(&key).cloned().map(|dom| {
      (dom.into_iter())
        .map(|sort| {
          let mut set = IdxBitSet::new();
          for c in sort {
            let c = self.alloc_copy(&&*c);
            let c: ClassId = self.alloc(c);
            set.union_with(&self.class_supers(c));
          }
          set
        })
        .collect::<Vec<_>>()
    });
    self.arity_cache.insert((a, c), val.clone());
    val
  }

  /// `Sorts.of_sort`: does `ty` inhabit the sort `s`?  For a type variable this is
  /// `sort_le` on its declared sort; for `Type (a, Ts)` it is the arities of `a`, whose
  /// domains are intersected over the classes of `s` (`mg_domain`) and then required of
  /// the arguments.
  fn of_sort(&mut self, ty: TypeId, s: SortId) -> bool {
    if s == SortId::TOP {
      return true
    }
    if let Some(&b) = self.of_sort_cache.get(&(ty, s)) {
      return b
    }
    let want = self.ctx[s].0.clone();
    let b = self.of_sort_set(ty, &want);
    self.of_sort_cache.insert((ty, s), b);
    b
  }

  fn of_sort_set(&mut self, ty: TypeId, want: &IdxBitSet<ClassId>) -> bool {
    match self.ctx[ty].0 {
      Type::Free(_, s) | Type::Var(_, s) => {
        // `sort_le`: every class wanted is entailed by one the variable declares
        let have = self.sort_closure(s);
        want.iter().all(|c| have.contains(c))
      }
      Type::Type(a, tys) => {
        // `mg_domain`: intersect the domains the wanted classes require
        let mut dom: Option<Vec<IdxBitSet<ClassId>>> = None;
        for c in want.iter() {
          let Some(ss) = self.arity(a, c) else { return false };
          match &mut dom {
            None => dom = Some(ss),
            Some(d) => {
              if d.len() != ss.len() {
                return false
              }
              for (x, y) in d.iter_mut().zip(&ss) {
                x.union_with(y)
              }
            }
          }
        }
        let Some(dom) = dom else { return true };
        if dom.len() != tys.len() {
          return false
        }
        (tys.to_vec().into_iter().zip(dom)).all(|(t, s)| self.of_sort_set(t, &s))
      }
    }
  }

  /// the statement of a theorem cited by serial: what the checker verified for it, brought
  /// into this theorem's interning tables
  fn cited(&mut self, i: u32) -> TermId {
    if let Some(&t) = self.cited_cache.get(&i) {
      return t
    }
    let v = (self.g.verified.get(&i)).unwrap_or_else(|| {
      panic!("citation of theorem {i}, which this run did not check")
    });
    let mut d = Decoder::new(v);
    let t = self.decode_term(&mut d);
    self.cited_cache.insert(i, t);
    t
  }

  /// Encode a statement so it can be carried across theorems (terms are interned per
  /// theorem, so ids mean nothing outside the checker that made them).  Tags mirror the
  /// `Term`/`Type` constructors; lengths and indices are LEB128.
  fn encode(
    &self, e: &mut Encoder, prop: TermId, var_map: &[(TypeId, TypeId)], shyps: SortsId,
  ) {
    e.term(self, prop);
    e.int(var_map.len() as u32);
    for &(a, b) in var_map {
      e.ty(self, a);
      e.ty(self, b)
    }
    let ss = self.ctx[shyps].0.iter().collect::<Vec<_>>();
    e.int(ss.len() as u32);
    for s in ss {
      e.sort(self, s)
    }
  }

  /// the sort hypotheses a checked theorem was left with, as this checker's ids
  fn cited_shyps(&mut self, i: u32) -> SortsId {
    let v = (self.g.verified.get(&i)).expect("promise not checked");
    let mut d = Decoder::new(v);
    self.decode_term(&mut d);
    let n = d.int();
    for _ in 0..n {
      self.decode_type(&mut d);
      self.decode_type(&mut d);
    }
    let n = d.int();
    let mut bits = IdxBitSet::new();
    for _ in 0..n {
      let s = self.decode_sort(&mut d);
      bits.insert(s);
    }
    self.alloc(bits)
  }

  fn decode_sort(&mut self, d: &mut Decoder<'_>) -> SortId {
    let n = d.int();
    let mut bits = IdxBitSet::new();
    for _ in 0..n {
      let c = d.str(self);
      let c: ClassId = self.alloc(c);
      bits.insert(c);
    }
    self.alloc(bits)
  }

  fn decode_type(&mut self, d: &mut Decoder<'_>) -> TypeId {
    // a back-reference is not a node of its own, so it must not shift the numbering
    if d.peek() == 3 {
      d.byte();
      let i = d.int();
      return d.types[i as usize]
    }
    let ty = self.decode_type_inner(d);
    d.types.push(ty);
    ty
  }

  fn decode_type_inner(&mut self, d: &mut Decoder<'_>) -> TypeId {
    match d.byte() {
      0 => {
        let c = d.str(self);
        let n = d.int();
        let tys = (0..n).map(|_| self.decode_type(d)).collect::<Vec<_>>();
        self.alloc_copy(&Type::Type(c, &tys))
      }
      1 => {
        let x = d.str(self);
        let s = self.decode_sort(d);
        self.alloc(Type::Free(x, s))
      }
      2 => {
        let x = d.str(self);
        let i = d.int();
        let x = self.alloc((x, i));
        let s = self.decode_sort(d);
        self.alloc(Type::Var(x, s))
      }
      _ => unreachable!("type back-reference is handled by the caller"),
    }
  }

  fn decode_term(&mut self, d: &mut Decoder<'_>) -> TermId {
    if d.peek() == 6 {
      d.byte();
      let i = d.int();
      return d.terms[i as usize]
    }
    let t = self.decode_term_inner(d);
    d.terms.push(t);
    t
  }

  fn decode_term_inner(&mut self, d: &mut Decoder<'_>) -> TermId {
    match d.byte() {
      0 => {
        let c = d.str(self);
        let ty = self.decode_type(d);
        self.alloc(Term::Const(c, ty))
      }
      1 => {
        let x = d.str(self);
        let ty = self.decode_type(d);
        self.alloc(Term::Free(x, ty))
      }
      2 => {
        let x = d.str(self);
        let i = d.int();
        let x = self.alloc((x, i));
        let ty = self.decode_type(d);
        self.alloc(Term::Var(x, ty))
      }
      3 => {
        let i = d.int();
        self.alloc(Term::Bound(i))
      }
      4 => {
        let x = d.str(self);
        let ty = self.decode_type(d);
        let e = self.decode_term(d);
        self.alloc(Term::Abs(x, ty, e))
      }
      5 => {
        let f = self.decode_term(d);
        let u = self.decode_term(d);
        self.alloc(Term::App(f, u))
      }
      _ => unreachable!("term back-reference is handled by the caller"),
    }
  }

  /// `Envir.eta_long`: the long eta normal form -- every subterm eta-expanded to the arity
  /// of its type.  Memoised on the local context, since the terms are hash-consed DAGs and
  /// expanding one as a tree is exponential.
  fn eta_long(&mut self, lctx: LCtxId, t: TermId) -> TermId {
    if let Some(&t) = self.eta_long_cache.get(&(lctx, t)) {
      return t
    }
    let out = self.eta_long_inner(lctx, t);
    self.eta_long_cache.insert((lctx, t), out);
    out
  }

  fn eta_long_inner(&mut self, lctx: LCtxId, t: TermId) -> TermId {
    if let Term::Abs(x, ty, e) = self.ctx[t].0 {
      let lctx2 = self.mk_lctx(lctx, ty);
      let e = self.eta_long(lctx2, e);
      return self.alloc(Term::Abs(x, ty, e))
    }
    let mut args = vec![];
    let mut head = t;
    while let Term::App(f, u) = self.ctx[head].0 {
      args.push(u);
      head = f
    }
    args.reverse();
    if matches!(self.ctx[head].0, Term::Abs(..)) {
      // a redex at the head: normalise it first, as `Envir.eta_long` does
      let t = BetaNorm::new().apply(self, t);
      return self.eta_long(lctx, t)
    }
    // the argument types still missing from `t`'s type
    let mut ty = self.get_type_ctx(lctx, t);
    let mut us = vec![];
    while let Some((a, b)) = self.try_dest_fun(ty) {
      us.push(a);
      ty = b
    }
    let i = us.len() as u32;
    let mut inc = IncrBound::new();
    let head = inc.apply0(self, head, i);
    // under the new binders the context is `rev us @ lctx`
    let mut lctx2 = lctx;
    for &u in &us {
      lctx2 = self.mk_lctx(lctx2, u)
    }
    let mut out = head;
    for &a in &args {
      let a = inc.apply0(self, a, i);
      let a = self.eta_long(lctx2, a);
      out = self.alloc(Term::App(out, a))
    }
    for j in (0..i).rev() {
      let b = self.alloc(Term::Bound(j));
      let b = self.eta_long(lctx2, b);
      out = self.alloc(Term::App(out, b))
    }
    let x = self.alloc("x");
    for &u in us.iter().rev() {
      out = self.alloc(Term::Abs(x, u, out))
    }
    out
  }

  /// `Type.legacy_freeze`: name a fresh `TFree` for each `TVar`, avoiding the `TFree`s
  /// already there (`Name.variant_list`), in order of occurrence
  fn legacy_freeze_names(&mut self, t: TermId) -> HashMap<IndexNameId, StringId> {
    let mut used: Vec<String> = vec![];
    let mut tvars: Vec<IndexNameId> = vec![];
    self.add_tfree_tvar_names(t, &mut used, &mut tvars, &mut HashSet::new());
    let mut out = HashMap::new();
    for v in tvars {
      let (x, i) = self.ctx[v].0;
      // `Term.string_of_indexname`
      let base = if i == 0 {
        self.ctx.strings.0[x].0.to_string()
      } else {
        format!("{}_{i}", self.ctx.strings.0[x].0)
      };
      let name = variant_name(&base, &used);
      used.push(name.clone());
      let name = self.alloc_copy(&&*name);
      out.insert(v, name);
    }
    out
  }

  /// the `TFree` names and the `TVar`s of a term, in order of occurrence
  fn add_tfree_tvar_names(
    &mut self, t: TermId, frees: &mut Vec<String>, vars: &mut Vec<IndexNameId>,
    seen: &mut HashSet<TermId>,
  ) {
    if !seen.insert(t) {
      return
    }
    match self.ctx[t].0 {
      Term::Const(_, ty) | Term::Free(_, ty) | Term::Var(_, ty) => {
        self.add_tfree_tvar_names_ty(ty, frees, vars)
      }
      Term::Abs(_, ty, e) => {
        self.add_tfree_tvar_names_ty(ty, frees, vars);
        self.add_tfree_tvar_names(e, frees, vars, seen)
      }
      Term::App(f, u) => {
        self.add_tfree_tvar_names(f, frees, vars, seen);
        self.add_tfree_tvar_names(u, frees, vars, seen)
      }
      Term::Bound(_) => {}
    }
  }

  fn add_tfree_tvar_names_ty(
    &mut self, ty: TypeId, frees: &mut Vec<String>, vars: &mut Vec<IndexNameId>,
  ) {
    match self.ctx[ty].0 {
      Type::Type(_, tys) => {
        for &ty in tys {
          self.add_tfree_tvar_names_ty(ty, frees, vars)
        }
      }
      Type::Free(x, _) => {
        let x = self.ctx.strings.0[x].0.to_string();
        if !frees.contains(&x) {
          frees.push(x)
        }
      }
      Type::Var(x, _) => {
        if !vars.contains(&x) {
          vars.push(x)
        }
      }
    }
  }

  /// `Thm.union_tpairs`: `Library.merge` of two flex-flex lists -- append the entries of
  /// the second that the first does not already have (up to alpha)
  fn union_tpairs(&mut self, t1: TpairsId, t2: TpairsId) -> TpairsId {
    if t1 == t2 || t2 == TpairsId::EMPTY {
      return t1
    }
    if t1 == TpairsId::EMPTY {
      return t2
    }
    let (l1, l2) = (self.ctx[t1].0.clone(), self.ctx[t2].0.clone());
    let mut out = l1.to_vec();
    for &(t, u) in &l2 {
      if !out.clone().iter().any(|&(t2, u2)| {
        (t == t2 || self.aconv(t, t2, &mut HashSet::new()))
          && (u == u2 || self.aconv(u, u2, &mut HashSet::new()))
      }) {
        out.push((t, u))
      }
    }
    self.alloc(out.into_boxed_slice())
  }

  /// `Thm.attach_tpairs`: `⟦t1 ≡ u1; …⟧ ⟹ prop`, the form in which `varifyT_global` and
  /// `legacy_freezeT` transform a theorem's flex-flex pairs along with its statement
  fn attach_tpairs(&mut self, tpairs: TpairsId, prop: TermId) -> TermId {
    let mut t = prop;
    for &(a, b) in self.ctx[tpairs].0.clone().iter().rev() {
      let eq = self.mk_eq(a, b);
      t = self.mk_imp(eq, t)
    }
    t
  }

  /// the inverse of [`attach_tpairs`](Self::attach_tpairs)
  fn detach_tpairs(&mut self, n: usize, mut prop: TermId) -> (TpairsId, TermId) {
    let mut out = vec![];
    for _ in 0..n {
      let (eq, rest) = self.dest_imp(prop);
      out.push(self.dest_eq(eq));
      prop = rest
    }
    (self.alloc(out.into_boxed_slice()), prop)
  }

  /// map every flex-flex pair through a term operation
  fn map_tpairs(
    &mut self, f: &mut impl FnMut(&mut Self, TermId) -> TermId, tpairs: TpairsId,
  ) -> TpairsId {
    if tpairs == TpairsId::EMPTY {
      return tpairs
    }
    let l = self.ctx[tpairs].0.clone();
    let out: Vec<_> = l.iter().map(|&(a, b)| (f(self, a), f(self, b))).collect();
    self.alloc(out.into_boxed_slice())
  }

  /// `Thm.dest_state`: split a proof state `⟦B1; …; Bn⟧ ⟹ C` at subgoal `i`, into the
  /// premises before it, the subgoal itself, and everything after it
  fn dest_state(&self, state: TermId, i: u32) -> (Vec<TermId>, TermId, TermId) {
    let mut bs = vec![];
    let mut st = state;
    for _ in 0..i - 1 {
      let (h, t) = self.dest_imp(st);
      bs.push(h);
      st = t
    }
    let (bi, c) = self.dest_imp(st);
    (bs, bi, c)
  }

  /// `Thm.norm_term_skip`: normalise under the unifier, but skip the outermost `n`
  /// assumptions -- they were lifted over from the goal, so the unifier (which assigns
  /// nothing below the state's maxidx) cannot touch them.  Parameter types *are*
  /// normalised, since flattening may have introduced new ones.
  fn norm_term_skip(
    &mut self, inst: &mut Mapper<TermId, InstTerm>, n: u32, t: TermId,
  ) -> TermId {
    if n == 0 {
      return inst.apply(self, t)
    }
    if let Some((_, e)) = self.try_dest_forall(t) {
      if let Term::Abs(a, ty, body) = self.ctx[e].0 {
        let ty = inst.f.ty.apply(self, ty);
        let body = self.norm_term_skip(inst, n, body);
        return self.mk_forall(a, ty, body)
      }
    }
    if let Some((a, b)) = self.try_dest_imp(t) {
      let b = self.norm_term_skip(inst, n - 1, b);
      return self.mk_imp(a, b)
    }
    panic!("norm_term_skip: too few assumptions")
  }

  /// `Term.rlist_abs`: close a term over the parameters stripped by [`strip_all`],
  /// turning each `⋀`-bound variable into a `λ`
  fn close_params(&mut self, params: &[(StringId, TypeId)], mut t: TermId) -> TermId {
    for &(x, ty) in params.iter().rev() {
      t = self.alloc(Term::Abs(x, ty, t))
    }
    t
  }

  /// `Thm.strip_assums2`: drop the assumptions and parameters that the two sides of a
  /// disagreement pair have in common because the rule was lifted over them.  The
  /// premises are dropped without being compared -- lifting made them equal by
  /// construction -- and only the shortened pair is unified.
  fn strip_assums2(&mut self, t1: TermId, t2: TermId) -> (TermId, TermId) {
    if let (Some((_, b1)), Some((_, b2))) = (self.try_dest_imp(t1), self.try_dest_imp(t2)) {
      return self.strip_assums2(b1, b2)
    }
    if let (Some((_, e1)), Some((_, e2))) = (self.try_dest_forall(t1), self.try_dest_forall(t2)) {
      if let Term::Abs(a, ty, u1) = self.ctx[e1].0 {
        if let Term::Abs(_, _, u2) = self.ctx[e2].0 {
          let (r1, r2) = self.strip_assums2(u1, u2);
          return (self.alloc(Term::Abs(a, ty, r1)), self.alloc(Term::Abs(a, ty, r2)))
        }
      }
    }
    (t1, t2)
  }

  /// `Term.strip_abs_body`
  fn strip_abs_body(&self, mut t: TermId) -> TermId {
    while let Term::Abs(_, _, b) = self.ctx[t].0 {
      t = b
    }
    t
  }

  /// `Term.match_bvs`: pair up the binder names of two terms.  ML builds its list by
  /// consing, so the pairs come out in the reverse of the order they are visited -- and
  /// the order matters, since `distinct`/`Symtab.make_distinct` downstream keep the
  /// *first* entry for a name.  The caller reverses.
  fn match_bvs(&mut self, t1: TermId, t2: TermId, al: &mut Vec<(StringId, StringId)>) {
    if let Term::Abs(x, _, s) = self.ctx[t1].0 {
      if let Term::Abs(y, _, t) = self.ctx[t2].0 {
        let empty = self.alloc("");
        if x != empty && y != empty {
          al.push((x, y))
        }
        self.match_bvs(s, t, al)
      }
      return
    }
    if let Term::App(f, s) = self.ctx[t1].0 {
      if let Term::App(g, t) = self.ctx[t2].0 {
        self.match_bvs(s, t, al);
        self.match_bvs(f, g, al)
      }
    }
  }

  /// `Thm.strip_lifted`: the part of `A` below the assumptions and parameters it was
  /// lifted over
  fn strip_lifted(&self, b: TermId, a: TermId) -> TermId {
    if let (Some((_, b1)), Some((_, a1))) = (self.try_dest_imp(b), self.try_dest_imp(a)) {
      return self.strip_lifted(b1, a1)
    }
    if let (Some((_, e1)), Some((_, e2))) = (self.try_dest_forall(b), self.try_dest_forall(a)) {
      if let Term::Abs(_, _, u1) = self.ctx[e1].0 {
        if let Term::Abs(_, _, u2) = self.ctx[e2].0 {
          return self.strip_lifted(u1, u2)
        }
      }
    }
    a
  }

  /// the base names of the schematic variables of a term
  fn add_var_names(&self, t: TermId, out: &mut HashSet<StringId>) {
    match self.ctx[t].0 {
      Term::Var(x, _) => {
        out.insert(self.ctx[x].0 .0);
      }
      Term::Abs(_, _, b) => self.add_var_names(b, out),
      Term::App(f, u) => {
        self.add_var_names(f, out);
        self.add_var_names(u, out)
      }
      _ => {}
    }
  }

  /// `Thm.strip_apply f B A`: strip off the assumptions and parameters that lifting over
  /// `B` introduced into `A`, and apply `f` to what is left
  fn strip_apply(
    &mut self, ren: &mut Mapper<TermId, RenameBvars>, b: TermId, a: TermId,
  ) -> TermId {
    if let (Some((_, b1)), Some((a2, b2))) = (self.try_dest_imp(b), self.try_dest_imp(a)) {
      let rest = self.strip_apply(ren, b1, b2);
      return self.mk_imp(a2, rest)
    }
    if let (Some((_, e1)), Some((_, e2))) = (self.try_dest_forall(b), self.try_dest_forall(a)) {
      if let Term::Abs(_, _, u1) = self.ctx[e1].0 {
        if let Term::Abs(x, ty, u2) = self.ctx[e2].0 {
          let rest = self.strip_apply(ren, u1, u2);
          return self.mk_forall(x, ty, rest)
        }
      }
    }
    ren.apply(self, a)
  }

  /// `Thm.rename_bvs`/`rename_bvars`: resolution renames a rule's bound variables -- and
  /// some of its schematic variables -- to the goal's parameter names.  The renaming is
  /// recorded nowhere, so it has to be recomputed to check the new subgoals against the
  /// rule's own premises.
  fn rename_bvars(
    &mut self, dpairs: &[(TermId, TermId)], b: TermId, as0: &[TermId],
  ) -> Option<RenameBvars> {
    let mut al = vec![];
    for &(t1, t2) in dpairs.iter().rev() {
      let (t1, t2) = (self.strip_abs_body(t1), self.strip_abs_body(t2));
      let mut al1 = vec![];
      self.match_bvs(t1, t2, &mut al1);
      al1.reverse();
      al1.append(&mut al);
      al = al1
    }
    if al.is_empty() {
      return None
    }
    // unknowns of the dpairs' left-hand sides (and of the flex-flex pairs) are preserved
    let mut unknowns = HashSet::new();
    for &(t1, _) in dpairs {
      self.add_var_names(t1, &mut unknowns)
    }
    // unknowns appearing in the premises themselves may be renamed
    let mut unknowns2 = HashSet::new();
    for &a in as0 {
      let a = self.strip_lifted(b, a);
      self.add_var_names(a, &mut unknowns2)
    }
    let mut seen = HashSet::new();
    let al2: Vec<_> = (al.iter())
      .filter(|&&(x, y)| unknowns2.contains(&x) && !unknowns.contains(&x) && !unknowns.contains(&y))
      .filter(|&&(x, _)| seen.insert(x))
      .copied()
      .collect();
    // `del_clashing`: drop renamings that would make two schematic variables collide,
    // rescanning until a pass introduces no new clash
    let mut xs: HashSet<_> = unknowns2.iter().copied().filter(|x| !al2.iter().any(|p| p.0 == *x)).collect();
    let mut ps = al2;
    let mut al3 = loop {
      let mut ys = xs.clone();
      let mut clash = false;
      let mut qs = vec![];
      for (x, y) in ps {
        if ys.contains(&y) {
          clash = true;
          xs.insert(x);
          ys.insert(x);
        } else {
          ys.insert(y);
          qs.push((x, y))
        }
      }
      qs.reverse();
      if !clash {
        break qs
      }
      ps = qs
    };
    al3.reverse();
    let mut vars = HashMap::new();
    for (x, y) in al3 {
      vars.entry(x).or_insert(y);
    }
    let mut bounds = HashMap::new();
    for &(x, y) in &al {
      bounds.entry(x).or_insert(y);
    }
    if vars.iter().all(|(x, y)| x == y) && bounds.iter().all(|(x, y)| x == y) {
      return None
    }
    Some(RenameBvars { vars, bounds })
  }

  /// `Logic.strip_params`: the `⋀`-bound parameters, descending through `⟹` as well.
  fn strip_params(&self, mut a: TermId, out: &mut Vec<(StringId, TypeId)>) {
    loop {
      if let Some((_, b)) = self.try_dest_imp(a) {
        a = b
      } else if let Some((_, e)) = self.try_dest_forall(a) {
        let Term::Abs(x, ty, t) = self.ctx[e].0 else { break };
        out.push((x, ty));
        a = t
      } else {
        break
      }
    }
  }

  /// `Logic.remove_params`: drop `j` leading parameters and the `n`-th premise, shifting the
  /// premises that survive over the removed binders.
  fn remove_params(&mut self, j: u32, n: i64, a: TermId) -> TermId {
    if j == 0 && n <= 0 {
      return a;
    }
    if let Some((h, b)) = self.try_dest_imp(a) {
      let b = self.remove_params(j, n - 1, b);
      if n == 1 {
        b
      } else {
        let h = IncrBound::new().apply0(self, h, j);
        self.mk_imp(h, b)
      }
    } else if let Some((_, e)) = self.try_dest_forall(a) {
      let Term::Abs(_, _, t) = self.ctx[e].0 else { panic!("expected abstraction under Pure.all") };
      self.remove_params(j - 1, n, t)
    } else {
      assert!(n <= 0, "remove_params: not enough premises");
      a
    }
  }

  /// `Logic.flatten_params`: move the parameters of a subgoal to the front, dropping the
  /// `n`-th premise (`n = 0` keeps them all). Parameter names are irrelevant here, since
  /// every comparison in this checker is up to alpha.
  fn flatten_params(&mut self, n: u32, a: TermId) -> TermId {
    let mut params = vec![];
    self.strip_params(a, &mut params);
    let mut body = self.remove_params(params.len() as u32, n as i64, a);
    for &(x, ty) in params.iter().rev() {
      body = self.mk_forall(x, ty, body)
    }
    body
  }

  fn try_dest_forall(&self, a: TermId) -> Option<(TypeId, TermId)> {
    let (f, e) = self.try_dest_app(a)?;
    let (c, ty) = self.try_dest_const(f)?;
    if c != StringId::ALL {
      return None;
    }
    let (ty, _) = self.try_dest_fun(ty)?;
    let (qary, _) = self.try_dest_fun(ty)?;
    Some((qary, e))
  }

  fn dest_forall(&self, a: TermId) -> (TypeId, TermId) {
    self.try_dest_forall(a).expect("expected forall")
  }

  fn dest_ofclass(&mut self, a: TermId) -> (TypeId, ClassId) {
    let (c, ty) = self.dest_const(self.dest_app(a).0);
    let &[ty] = self.dest_type(self.dest_fun(ty).0).1;
    let cl = self.ctx[c].0.strip_suffix("_class").expect("expected FOO_class");
    let s = self.alloc(cl);
    (ty, self.alloc(s))
  }

  fn try_dest_eq(&self, a: TermId) -> Option<(TermId, TermId)> {
    let (f, rhs) = self.try_dest_app(a)?;
    let (f, lhs) = self.try_dest_app(f)?;
    let (c, _) = self.try_dest_const(f)?;
    if c != StringId::EQ {
      return None;
    }
    Some((lhs, rhs))
  }

  fn dest_eq(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_eq(a).expect("expected equality")
  }

  /// Alpha-equivalence, without the panic of [`AConv`]: terms are hash-consed, so this is
  /// only reached when bound-variable names differ.
  fn aconv(&self, a: TermId, b: TermId, seen: &mut HashSet<(TermId, TermId)>) -> bool {
    if a == b {
      return true;
    }
    if !seen.insert((a, b)) {
      return true;
    }
    match (&self.ctx[a].0, &self.ctx[b].0) {
      (&Term::Abs(_, ty1, e1), &Term::Abs(_, ty2, e2)) => {
        ty1 == ty2 && self.aconv(e1, e2, seen)
      }
      (&Term::App(f1, u1), &Term::App(f2, u2)) => {
        self.aconv(f1, f2, seen) && self.aconv(u1, u2, seen)
      }
      _ => false,
    }
  }

  /// `Name.clean_index`: an internal name carries one trailing `_` per index bump
  /// (`Name.internal = suffix "_"`), so generalizing `uu_` at index 0 yields `?uu.1`.
  fn clean_index(&mut self, x: StringId, idx: u32) -> IndexNameId {
    let name = self.ctx[x].0;
    let mut clean = name;
    let mut i = idx;
    while let Some(s) = clean.strip_suffix('_') {
      clean = s;
      i += 1
    }
    let x = if clean.len() == name.len() { x } else { self.alloc_copy(&clean) };
    self.alloc((x, i))
  }

  /// `Term.loose_bvar1 (t, lev)`: does the bound variable `lev` occur loose in `t`?
  fn loose_bvar1(&self, t: TermId, lev: u32) -> bool {
    match self.ctx[t].0 {
      Term::Bound(i) => i == lev,
      Term::Abs(_, _, e) => self.loose_bvar1(e, lev + 1),
      Term::App(f, u) => self.loose_bvar1(f, lev) || self.loose_bvar1(u, lev),
      _ => false,
    }
  }

  /// `Envir.decr_same`: decrement loose bound variables at or above `lev`.
  fn decr_bound(&mut self, t: TermId, lev: u32) -> TermId {
    match self.ctx[t].0 {
      Term::Bound(i) if i >= lev => self.alloc(Term::Bound(i - 1)),
      Term::Abs(x, ty, e) => {
        let e = self.decr_bound(e, lev + 1);
        self.alloc(Term::Abs(x, ty, e))
      }
      Term::App(f, u) => {
        let f = self.decr_bound(f, lev);
        let u = self.decr_bound(u, lev);
        self.alloc(Term::App(f, u))
      }
      _ => t,
    }
  }

  /// Does `x` occur in `t`? Used for the eigenvariable condition of `abstract_rule`.
  fn occurs(&self, x: TermId, t: TermId, seen: &mut HashSet<TermId>) -> bool {
    if x == t {
      return true;
    }
    if !seen.insert(t) {
      return false;
    }
    match self.ctx[t].0 {
      Term::Abs(_, _, e) => self.occurs(x, e, seen),
      Term::App(f, a) => self.occurs(x, f, seen) || self.occurs(x, a, seen),
      _ => false,
    }
  }

  fn mk_eq(&mut self, a: TermId, b: TermId) -> TermId {
    // not `TermData::ty`: that is blocked for a term whose type only follows from the
    // local context (e.g. a beta redex under a binder)
    let ty = self.get_type_ctx(LCtxId::NIL, a);
    let ty2 = self.mk_fun(ty, TypeId::PROP);
    let ty2 = self.mk_fun(ty, ty2);
    let eq = self.alloc(Term::Const(StringId::EQ, ty2));
    let f = self.alloc(Term::App(eq, a));
    self.alloc(Term::App(f, b))
  }

  fn union<I: BitSetIdx<'a>, D>(&mut self, s1: I, s2: I) -> I
  where
    CheckerCtx<'a>: std::ops::Index<I, Output = (IdxBitSet<I::Elem>, D)>,
  {
    if s1 == I::EMPTY || s1 == s2 {
      s2
    } else if s2 == I::EMPTY {
      s1
    } else {
      let mut sorts = self.ctx[s1].0.clone();
      sorts.union_with(&self.ctx[s2].0);
      self.alloc(sorts)
    }
  }

  fn get_type_ctx(&mut self, lctx: LCtxId, t: TermId) -> TypeId {
    (self.try_get_type_ctx(lctx, t)).expect("expected function type")
  }

  fn try_get_type_ctx(&mut self, lctx: LCtxId, t: TermId) -> Option<TypeId> {
    let tdata = &self.ctx[t];
    if let Ok(ty) = tdata.1.ty {
      return Some(ty);
    }
    if let Some(&ty) = self.type_cache.get(&(lctx, t)) {
      return Some(ty);
    }
    let ty = match tdata.0 {
      Term::Const(_, _) | Term::Free(_, _) | Term::Var(_, _) => unreachable!(),
      Term::Bound(mut i) => {
        let mut lctx = lctx;
        loop {
          let LCtx::Cons(p, ty) = self.ctx[lctx].0 else { panic!() };
          if i == 0 {
            break ty;
          }
          i -= 1;
          lctx = p;
        }
      }
      Term::Abs(_, dom, e) => {
        let lctx2 = self.mk_lctx(lctx, dom);
        let ty = self.try_get_type_ctx(lctx2, e)?;
        self.mk_fun(dom, ty)
      }
      Term::App(e1, _) => {
        let ty = self.try_get_type_ctx(lctx, e1)?;
        match self.ctx[ty].0 {
          Type::Type(StringId::FUN, &[_, rng]) => rng,
          _ => return None,
        }
      }
    };
    self.type_cache.insert((lctx, t), ty);
    Some(ty)
  }

  /// Intern a hypothesis.  ML's hypothesis set is an `Ord_List` over
  /// `Term_Ord.fast_term_ord`, which does not compare `Abs` binder names (that is
  /// `comments_ord`, used only by `syntax_term_ord`), so alpha-variant hypotheses are *one*
  /// element: `union_hyps` merges them and `implies_intr` discharges either.  Terms here
  /// are hash-consed with their binder names, so hyps are interned under a canonical one.
  /// Resolution makes this reachable -- `rename_bvars` renames a rule's bound variables to
  /// the goal's parameter names, so the same assumption arrived at two ways differs.
  fn hyp(&mut self, t: TermId) -> HypId {
    let t = Mapper::new(CanonBinders).apply(self, t);
    self.alloc(t)
  }

  /// hypotheses are propositions; the stronger "no schematic variables" condition belongs
  /// to `Thm.assume` alone (`implies_intr` happily discharges a prop containing variables)
  fn check_hyp(&mut self, t: TermId) {
    let data = &self.ctx[t].1;
    assert!(self.ctx[data.ty.unwrap()].0.as_type().0 == StringId::PROP, "hypothesis is not a prop");
  }

  /// the `sorts` of the cterm a rule consumed: inherited through cterm operations, so it
  /// cannot be recovered from the term itself and the exporter records it
  fn parse_sorts<'b>(
    &mut self, m: &mut Mapping, bp: &BinParser<'b>, sorts: TagPtr,
  ) -> SortsId {
    let mut bits = IdxBitSet::new();
    for s in bp.parse_list(sorts) {
      let s: SortId = self.parse(m, bp, s);
      bits.insert(s);
    }
    self.alloc(bits)
  }

  fn parse<'b, 'c, T: BinParse<'b, BM<'a, 'c>>>(
    &'c mut self, m: &'c mut Mapping, bp: &BinParser<'b>, p: TagPtr,
  ) -> T {
    T::parse(&mut (self, m), bp, p)
  }

  /// what a theorem's trace *claims* it proves, without checking the proof: used to keep
  /// reporting sane when a check fails, so that its users are compared against the claim
  /// and the failure is counted once
  pub fn claim(&mut self, bp: &BinParser<'_>, tr: TagPtr) -> VerifiedThm {
    let mut m = Mapping::default();
    let tr: ThmTrace = self.parse(&mut m, bp, tr);
    let mut e = Encoder::default();
    self.encode(&mut e, tr.header.prop, &tr.unconstrain_var_map, SortsId::EMPTY);
    e.finish(tr.unconstrain_shyps)
  }

  pub fn check(&mut self, bp: &BinParser<'_>, tr: TagPtr) -> VerifiedThm {
    let mut m = Mapping::default();
    let tr: ThmTrace = self.parse(&mut m, bp, tr);
    println!(
      "proof_trace/{} = {}.{}",
      tr.header.serial, self.ctx.strings.0[tr.header.thm_name.name].0, tr.header.thm_name.i,
    );
    if *DEBUG_TRACE {
      println!("{}", pretty(&tr));
    }
    let trace::Header { mut prop, .. } = tr.header;
    let mut visited = BTreeSet::new();
    let mut stack = vec![tr.root];
    while let Some(p) = stack.pop() {
      if visited.insert(p) {
        stack.extend(proof::subproofs(bp, p))
      }
    }
    for pf in visited {
      #[allow(non_upper_case_globals)]
      if *DEBUG_STEPS {
        println!("  -> rule {}", bp.get_enum(pf).0);
      }
      let pf2 = match bp.get_enum(pf) {
        (proof::ZProp, &[prop, shyps, tpairs, p]) => {
          let cp = self.ctx[m.proofs[&p]].0.clone();
          let inner = bp.get_enum(p).0;

          let recorded: TermId = self.parse(&mut m, bp, prop);
          if !self.aconv(recorded, cp.concl, &mut HashSet::new()) {
            println!("!! statement mismatch after rule {inner}");
            println!("   computed: {:?}", self.pp(cp.concl));
            println!("   recorded: {:?}", self.pp(recorded));
            if inner == proof::Bicompose {
              let (_, args) = bp.get_enum(p);
              let a: BicomposeArgs = self.parse(&mut m, bp, args[0]);
              for &(v, vs, ty) in &a.env.tysubst {
                println!("   env tyvar {:?}:{:?} := {:?}", self.pp(v), self.pp(vs), self.pp(ty));
              }
              for &(v, vt, tm) in &a.env.subst {
                println!("   env var   {:?}:{:?} := {:?}", self.pp(v), self.pp(vt), self.pp(tm));
              }
              println!("   nbs={} nsubgoal={} flatten={} n={}", a.nbs, a.nsubgoal, a.flatten, a.n);
            }
            if inner == proof::Instantiate {
              let (_, args) = bp.get_enum(p);
              let sub = Subst::from_assoc(&mut (&mut *self, &mut m), bp, args[0], args[1]);
              for &(v, vs, ty) in &sub.tysubst {
                println!("   tysubst {:?}:{:?} := {:?}", self.pp(v), self.pp(vs), self.pp(ty));
              }
              for &(v, vt, tm) in &sub.subst {
                println!("   subst   {:?}:{:?} := {:?}", self.pp(v), self.pp(vt), self.pp(tm));
              }
            }
            panic!("statement mismatch at rule {inner}");
          }

          // compare modulo the trivial sort: an unconstrained type variable contributes the
          // empty class set, which is satisfied by everything and which the final
          // unconstrain check skips as well
          let mut want = IdxBitSet::new();
          for s in bp.parse_list(shyps) {
            let s: SortId = self.parse(&mut m, bp, s);
            if s != SortId::TOP {
              want.insert(s);
            }
          }
          let mut got = self.ctx[cp.shyps].0.clone();
          got.remove(SortId::TOP);
          // The sort hypotheses must match exactly: Isabelle's shyps is what the recorded
          // constraints were derived from, so anything else makes the final unconstrain
          // reconciliation meaningless.  Note this is *not* the same as recomputing the
          // sorts of the statement -- Cterm.sorts is inherited through cterm operations, so
          // a rule consuming a cterm contributes sorts that its term no longer mentions.
          if want != got {
            let invented =
              got.iter().filter(|&s| !want.contains(s)).map(|s| self.pp(s)).collect::<Vec<_>>();
            let dropped =
              want.iter().filter(|&s| !got.contains(s)).map(|s| self.pp(s)).collect::<Vec<_>>();
            println!("!! sort hypotheses differ after rule {inner}");
            if !invented.is_empty() {
              println!("   invented: {invented:?}");
            }
            if !dropped.is_empty() {
              println!("   dropped:  {dropped:?}");
            }
            println!("   for:      {:?}", self.pp(cp.concl));
            // did the *input* to this rule already differ?  If its subproofs are wrapped,
            // their recorded shyps were checked and matched, so a divergence here is the
            // rule's own doing; an unwrapped subproof is an untraced boundary instead.
            for &sp in proof::subproofs(bp, p) {
              let (tag, args) = bp.get_enum(sp);
              let ours = self.pp(self.ctx[m.proofs[&sp]].0.shyps);
              if tag == proof::ZProp {
                let rec = self.parse_sorts(&mut m, bp, args[1]);
                println!("   subproof: ZProp over rule {} recorded {:?}, ours {ours:?}",
                  bp.get_enum(args[3]).0, self.pp(rec));
              } else {
                println!("   subproof: rule {tag} is UNWRAPPED, ours {ours:?}");
              }
            }
            panic!("shyps mismatch at rule {inner}");
          }

          // the flex-flex pairs must match exactly, in order: they are what `FlexFlex`
          // later discharges, and a dropped pair is a dropped proof obligation
          let want: Vec<(TermId, TermId)> =
            bp.parse_list(tpairs).map(|t| self.parse(&mut m, bp, t)).collect();
          let got = self.ctx[cp.tpairs].0.clone();
          if want.len() != got.len()
            || (want.iter().zip(&got)).any(|(&(a1, b1), &(a2, b2))| {
              !self.aconv(a1, a2, &mut HashSet::new()) || !self.aconv(b1, b2, &mut HashSet::new())
            })
          {
            println!("!! flex-flex mismatch after rule {inner}");
            println!("   computed: {:?}", got.iter().map(|&(a, b)| (self.pp(a), self.pp(b)))
              .collect::<Vec<_>>());
            println!("   recorded: {:?}", want.iter().map(|&(a, b)| (self.pp(a), self.pp(b)))
              .collect::<Vec<_>>());
            panic!("flex-flex mismatch at rule {inner}");
          }
          cp
        }
        (proof::Sorry, _) => {
          // find who has this Sorry as a subproof: with `prooftrace_props` on, the parent
          // is a ZProp carrying the statement of the step that went unrecorded
          let mut stack = vec![tr.root];
          let mut seen = BTreeSet::new();
          while let Some(q) = stack.pop() {
            if seen.insert(q) {
              for &r in proof::subproofs(bp, q) {
                if r == pf {
                  let (tag, args) = bp.get_enum(q);
                  if tag == proof::ZProp {
                    let t: TermId = self.parse(&mut m, bp, args[0]);
                    println!("!! unrecorded step proves {:?}", self.pp(t));
                  } else {
                    println!("!! unrecorded step is subproof of rule {tag}");
                  }
                }
                stack.push(r)
              }
            }
          }
          panic!(
          "encountered Sorry (unrecorded proof) in {}.{} at {}:{}",
          self.ctx.strings.0[tr.header.thm_name.name].0,
          tr.header.thm_name.i,
          self.ctx.strings.0[tr.header.command_pos.file].0,
          tr.header.command_pos.line,
        )
        }
        (proof::Pruned, _) => panic!("encountered Pruned (prune_proofs?)"),
        (proof::Hyp, &[concl, sorts]) => {
          let concl: TermId = self.parse(&mut m, bp, concl);
          // Thm.assume: "assume: variables" unless maxidx = ~1
          assert!(self.ctx[concl].1.maxidx == MaxIdx::NONE, "assume: variables");
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let hyp = self.hyp(concl);
          CProof {
            shyps,
            hyps: self.alloc(IdxBitSet::single(hyp)),
            tpairs: TpairsId::EMPTY,
            concl,
          }
        }
        (proof::ImpIntr, &[t, sorts, p]) => {
          let CProof { mut shyps, hyps, tpairs, mut concl } = self.ctx[m.proofs[&p]].0;
          let t: TermId = self.parse(&mut m, bp, t);
          let mut hyps = self.ctx[hyps].0.clone();
          let TermData { ty, .. } = self.ctx[t].1;
          assert_eq!(ty, Ok(TypeId::PROP));
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          shyps = self.union(shyps, sorts);
          hyps.remove(self.hyp(t));
          concl = self.mk_imp(t, concl);
          CProof { shyps, hyps: self.alloc(hyps), tpairs, concl }
        }
        (proof::ImpElim, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, tpairs: tp1, concl } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, tpairs: tp2, concl: lhs2 } = self.ctx[m.proofs[&q]].0;
          let shyps = self.union(shyps1, shyps2);
          let hyps = self.union(hyps1, hyps2);
          let tpairs = self.union_tpairs(tp1, tp2);
          let (lhs, concl) = self.dest_imp(concl);
          cmp_site("implies_elim: the premise vs the other theorem");
          Comparer::new(AConv).apply(self, lhs, lhs2);
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::ForallIntr, &[x, sorts, p]) => {
          let x: TermId = self.parse(&mut m, bp, x);
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          // as in `abstract_rule`, only the `Free` case is checked against the hypotheses
          if hyps != HypsId::EMPTY && matches!(self.ctx[x].0, Term::Free(..)) {
            let mut seen = HashSet::new();
            for h in self.ctx[hyps].0.clone().iter() {
              assert!(!self.occurs(x, self.ctx[h].0, &mut seen), "forall_intr: variable free in hyps")
            }
          }
          let name = match self.ctx[x].0 {
            Term::Free(n, _) => n,
            Term::Var(n, _) => self.ctx[n].0 .0,
            _ => panic!("forall_intr: expected a variable"),
          };
          let ty = self.ctx[x].1.ty.unwrap();
          let shyps = self.union(shyps, sorts);
          let body = AbstractOver::new(x).apply(self, concl, 0);
          CProof { shyps, hyps, tpairs, concl: self.mk_forall(name, ty, body) }
        }
        (proof::ForallElim, &[t, sorts, p]) => {
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let t: TermId = self.parse(&mut m, bp, t);
          let (ty2, pred) = self.dest_forall(concl);
          let TermData { ty, .. } = self.ctx[t].1;
          assert_eq!(ty, Ok(ty2));
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          let shyps = self.union(shyps, sorts);
          let concl = if let Term::Abs(_, _, body) = self.ctx[pred].0 {
            SubstBound::new(&[t]).apply(self, body, 0)
          } else {
            self.alloc(Term::App(pred, t))
          };
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::Axiom, &[name, concl, _src]) => {
          let name: StringId = self.parse(&mut m, bp, name);
          let concl: TermId = self.parse(&mut m, bp, concl);
          let shyps = self.ctx[concl].1.sorts;
          // `Thm.axiom'` looks the name up in `Theory.axiom_table` and uses the stored
          // proposition, which is what `theory/axioms` exports -- after `standard_prop`
          // has renamed the variables canonically, hence the comparison modulo renaming
          let nm = self.ctx.strings.0[name].0.to_string();
          match self.g.axiom_props.get(&nm) {
            Some(p) => {
              // `standard_prop` lifts the sorts of the type variables out into `typargs`,
              // so put them back before comparing
              let (want, typargs) = (p.prop.clone(), p.typargs.clone());
              self.axiom_sorts = typargs.into_iter().collect();
              let want = self.reify_axiom(&want);
              let (a, b) = (self.canon_stmt(want), self.canon_stmt(concl));
              if a != b && *DEBUG_STEPS {
                println!("!! axiom {nm}\n   declared: {:?}\n   used:     {:?}",
                  self.pp(a), self.pp(b));
              }
              assert!(a == b, "axiom {nm} does not state what the theory declares");
            }
            None => panic!("axiom {nm} is not declared by any theory in this session"),
          }
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::Oracle, &[name, t, sorts]) => {
          let name: StringId = self.parse(&mut m, bp, name);
          let concl: TermId = self.parse(&mut m, bp, t);
          assert!(self.ctx[concl].1.ty == Ok(TypeId::PROP), "oracle: the term must have type prop");
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          if *DEBUG_STEPS {
            println!("oracle {}: {:?}", self.ctx.strings.0[name].0, self.pp(concl));
          }
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::Refl, &[t, sorts]) => {
          let t = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let concl = self.mk_eq(t, t);
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::Symm, &[p]) => {
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let (t, u) = self.dest_eq(concl);
          CProof { shyps, hyps, tpairs, concl: self.mk_eq(u, t) }
        }
        (proof::Trans, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, tpairs: tp1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, tpairs: tp2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (t1, u1) = self.dest_eq(c1);
          let (u2, t2) = self.dest_eq(c2);
          cmp_site("combination: the two equations");
          Comparer::new(AConv).apply(self, u1, u2);
          let concl = self.mk_eq(t1, t2);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2),
            tpairs: self.union_tpairs(tp1, tp2), concl }
        }
        (proof::BetaNorm, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let rhs = BetaNorm::new().apply(self, t);
          let concl = self.mk_eq(t, rhs);
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::BetaHead, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let (f, u) = self.dest_app(t);
          let Term::Abs(_, _, b) = self.ctx[f].0 else { panic!("beta_conversion: not a redex") };
          let rhs = SubstBound::new(&[u]).apply(self, b, 0);
          let concl = self.mk_eq(t, rhs);
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::Eta, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let rhs = EtaContract::new().apply(self, t);
          let concl = self.mk_eq(t, rhs);
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::EtaLong, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let lctx = self.alloc(LCtx::Nil);
          let rhs = self.eta_long(lctx, t);
          let concl = self.mk_eq(t, rhs);
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::StripSHyps, &[sorts, p]) => {
          let CProof { mut shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          if *DEBUG_STEPS {
            let listed = bp
              .parse_list(sorts)
              .map(|s| {
                let s: SortId = self.parse(&mut m, bp, s);
                self.pp(s)
              })
              .collect::<Vec<_>>();
            println!("       strip removes {:?} from {:?}", listed, self.pp(shyps));
          }
          if sorts != TagPtr::ZERO {
            let mut newsorts = self.ctx[shyps].0.clone();
            for s in bp.parse_list(sorts) {
              newsorts.remove(self.parse(&mut m, bp, s));
            }
            newsorts.0.shrink_to_fit();
            shyps = self.alloc(newsorts);
          }
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::AbsRule, &[x, sorts, p]) => {
          let x: TermId = self.parse(&mut m, bp, x);
          // `Thm.abstract_rule` inherits the abstracted cterm's sorts
          // (`shyps = Sorts.union sorts shyps`), which are not recomputable from `x`
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let shyps = self.union(shyps, sorts);
          let (t, u) = self.dest_eq(concl);
          // `check_result a ts` is called with `ts = hyps` for a `Free` and `ts = []` for a
          // `Var` -- for a schematic variable the condition is about `tpairs` alone
          if hyps != HypsId::EMPTY && matches!(self.ctx[x].0, Term::Free(..)) {
            let mut seen = HashSet::new();
            for h in self.ctx[hyps].0.clone().iter() {
              assert!(!self.occurs(x, self.ctx[h].0, &mut seen), "abstract_rule: variable free in hyps")
            }
          }
          let name = match self.ctx[x].0 {
            Term::Free(n, _) => n,
            Term::Var(n, _) => self.ctx[n].0 .0,
            _ => panic!("abstract_rule: expected a variable"),
          };
          let ty = self.ctx[x].1.ty.unwrap();
          let t = AbstractOver::new(x).apply(self, t, 0);
          let u = AbstractOver::new(x).apply(self, u, 0);
          let f = self.alloc(Term::Abs(name, ty, t));
          let g = self.alloc(Term::Abs(name, ty, u));
          CProof { shyps, hyps, tpairs, concl: self.mk_eq(f, g) }
        }
        (proof::AppRule, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, tpairs: tp1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, tpairs: tp2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (f, g) = self.dest_eq(c1);
          let (t, u) = self.dest_eq(c2);
          // `Thm.combination` raises THM ("combination: types") unless `f : tT → _`
          let (dom, _) = self.dest_fun(self.ctx[f].1.ty.unwrap());
          assert!(dom == self.ctx[t].1.ty.unwrap(), "combination: types");
          let ft = self.alloc(Term::App(f, t));
          let gu = self.alloc(Term::App(g, u));
          let concl = self.mk_eq(ft, gu);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2),
            tpairs: self.union_tpairs(tp1, tp2), concl }
        }
        (proof::EqIntr, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, tpairs: tp1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, tpairs: tp2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (a1, b1) = self.dest_imp(c1);
          let (b2, a2) = self.dest_imp(c2);
          cmp_site("equal_intr: the two implications");
          let mut cmp = Comparer::new(AConv);
          cmp.apply(self, a1, a2);
          cmp.apply(self, b1, b2);
          let concl = self.mk_eq(a1, b1);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2),
            tpairs: self.union_tpairs(tp1, tp2), concl }
        }
        (proof::EqElim, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, tpairs: tp1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, tpairs: tp2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (a, b) = self.dest_eq(c1);
          cmp_site("equal_elim: the equation's lhs vs the other theorem");
          Comparer::new(AConv).apply(self, a, c2);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2),
            tpairs: self.union_tpairs(tp1, tp2), concl: b }
        }
        (proof::FlexFlex, &[env, p]) => {
          let env = Subst::from_env(&mut (&mut *self, &mut m), bp, env);
          let empty_env = env.tysubst.is_empty() && env.subst.is_empty();
          let sorts: Vec<_> = env.tysubst.iter().map(|&(_, _, ty)| ty).collect();
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          if empty_env {
            // `Envir.is_empty env` returns the theorem unchanged
            CProof { shyps, hyps, tpairs, concl }
          } else {
            let mut inst = Mapper::new(InstTerm::new(env, InstMode::Envir));
            self.check_env_sorts(&mut inst);
            let concl = inst.apply(self, concl);
            // trivial pairs `t ≡ t` are dropped, the rest survive normalised
            let l = self.ctx[tpairs].0.clone();
            let mut out = vec![];
            for &(a, b) in &l {
              let (a, b) = (inst.apply(self, a), inst.apply(self, b));
              if a != b && !self.aconv(a, b, &mut HashSet::new()) {
                out.push((a, b))
              }
            }
            let tpairs = self.alloc(out.into_boxed_slice());
            let mut shyps = shyps;
            for ty in sorts {
              shyps = self.union(shyps, self.ctx[ty].1.sorts)
            }
            CProof { shyps, hyps, tpairs, concl }
          }
        }
        (proof::Generalize, &[tfrees, frees, idx, p]) => {
          // `Names.set` is `int Table.table` (a 2-3 tree), not a list: exportSmall dumps the
          // table itself, where the old XML encoder flattened it via `Names.dest`.
          let tfrees: Table<StringId, u32> = self.parse(&mut m, bp, tfrees);
          let frees: Table<StringId, u32> = self.parse(&mut m, bp, frees);
          let idx: u32 = self.parse(&mut m, bp, idx);
          let CProof { concl: c0, .. } = self.ctx[m.proofs[&p]].0;
          // Thm.generalize raises "generalize: bad index" unless idx > maxidx, without
          // which the freshly created `Var (x, idx)` can collide with one already there.
          // (ML compares against the *theorem's* maxidx, which also covers its tpairs.)
          assert!(idx + 1 > self.ctx[c0].1.maxidx.0, "generalize: bad index");
          let mut inst = Mapper::new(GenTerm::new(
            tfrees.0.into_iter().map(|(x, _)| x).collect(),
            frees.0.into_iter().map(|(x, _)| x).collect(),
            idx,
          ));
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let tpairs = self.map_tpairs(&mut |ck, t| inst.apply(ck, t), tpairs);
          CProof { shyps, hyps, tpairs, concl: inst.apply(self, concl) }
        }
        (proof::Instantiate, &[args, p]) => {
          let &[tysubst, subst, sorts, beta] = bp.get(args.as_ptr()).as_tuple_n();
          // `Thm.instantiate` and `Thm.instantiate_beta` share this rule and differ only in
          // whether the substitution reduces the redexes it creates; `\<^instantiate>`
          // defaults to the beta variant, so the trace records which one ran
          let beta: bool = self.parse(&mut m, bp, beta);
          let subst = Subst::from_assoc(&mut (&mut *self, &mut m), bp, tysubst, subst);
          // `make_instT` raises TYPE ("instantiate: type not of sort") otherwise
          for &(_, s, ty) in &subst.tysubst {
            assert!(self.of_sort(ty, s), "instantiate: type not of sort");
          }
          let mut inst = Mapper::new(InstTerm::new(
            subst,
            if beta { InstMode::InstBeta } else { InstMode::Inst },
          ));
          let CProof { hyps, tpairs, concl, .. } = self.ctx[m.proofs[&p]].0;
          // Thm.instantiate sets shyps = shyps' outright, and prep_insts derives that from
          // the *certified* Ctyp/Cterm sorts, which are inherited and so cannot be
          // recomputed from the raw types and terms recorded here.
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          if *DEBUG_BC {
            for &(v, vs, ty) in &inst.f.ty.f.subst.clone() {
              println!("  [inst] tyvar {:?}:{:?} := {:?} contributing {:?}", self.pp(v),
                self.pp(vs), self.pp(ty), self.pp(self.ctx[ty].1.sorts));
            }
            for &(v, vt, tm) in &inst.f.subst.clone() {
              println!("  [inst] var {:?}:{:?} := {:?} contributing {:?}", self.pp(v),
                self.pp(vt), self.pp(tm), self.pp(self.ctx[tm].1.sorts));
            }
          }
          let tpairs = self.map_tpairs(&mut |ck, t| inst.apply(ck, t), tpairs);
          CProof { shyps, hyps, tpairs, concl: inst.apply(self, concl) }
        }
        (proof::Trivial, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          assert!(self.ctx[t].1.ty == Ok(TypeId::PROP), "trivial: the term must have type prop");
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let concl = self.mk_imp(t, t);
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::OfClass, &[ty, c]) => {
          let OfClassCache { itself, type_ } = self.ofclass_cache.unwrap_or_else(|| {
            let itself = self.alloc("itself");
            let type_ = self.alloc("Pure.type");
            *self.ofclass_cache.insert(OfClassCache { itself, type_ })
          });
          // the recorded class `c`, and the constant `c_class` that represents it in terms
          let cname = std::str::from_utf8(bp.get(c.as_ptr()).as_str()).unwrap().to_owned();
          let c = self.alloc_copy(&&*format!("{cname}_class"));
          let cls = self.alloc_copy(&&*cname);
          let cls: ClassId = self.alloc(cls);
          let ty: TypeId = self.parse(&mut m, bp, ty);
          // `Thm.of_class` raises THM ("of_class: type not of class …") otherwise
          let s = self.alloc(IdxBitSet::single(cls));
          assert!(self.of_sort(ty, s), "of_class: type not of class");
          let itself_t = self.alloc_copy(&Type::Type(itself, &[ty]));
          let cty = self.mk_fun(itself_t, TypeId::PROP);
          let c = self.alloc(Term::Const(c, cty));
          let ty2 = self.alloc(Term::Const(type_, itself_t));
          let concl: TermId = self.alloc(Term::App(c, ty2));
          CProof { shyps: self.ctx[concl].1.sorts, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::Promise, &[i, t, sorts]) => {
          let i = i.as_uint();
          let concl: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let proved = self.cited(i);
          cmp_site("promise: the forked proof's statement vs the promised one");
          Comparer::new(AConv).apply(self, proved, concl);
          let got = self.cited_shyps(i);
          assert!(
            self.ctx[got].0.is_subset(&self.ctx[shyps].0.clone()),
            "promise: the forked proof has more sort hypotheses than promised"
          );
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::Thm, &[i]) => {
          let i = i.as_uint();
          let concl = self.cited(i);
          let shyps = self.alloc(IdxBitSet::single(SortId::TOP));
          CProof { shyps, hyps: HypsId::EMPTY, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::ConstrainThm, &[i, shyps, hyps, prop]) => {
          let i = i.as_uint();
          // the referenced theorem's own sort hypotheses, which the using theorem inherits
          let shyps = self.parse_sorts(&mut m, bp, shyps);
          let mut hyp_terms = vec![];
          let mut bits = IdxBitSet::new();
          for h in bp.parse_list(hyps) {
            let h = self.parse(&mut m, bp, h);
            hyp_terms.push(h);
            bits.insert(self.hyp(h));
          }
          let hyps = self.alloc(bits);
          // `prepare_thm_proof` records `prop = Logic.list_implies (hyps, concl)`, and the
          // reference is used applied to those hypotheses (`argsP = … map Hyp hyps`).  So
          // strip them back off, keeping them as hypotheses -- leaving them as premises as
          // well would count each one twice.
          let mut concl: TermId = self.parse(&mut m, bp, prop);
          cmp_site("constrain_thm: recorded hypothesis vs the statement's premise");
          let mut cmp = Comparer::new(AConv);
          for &h in &hyp_terms {
            let (arg, rest) = self.dest_imp(concl);
            cmp.apply(self, h, arg);
            concl = rest
          }
          // and the citation must agree with what theorem `i` was verified to prove --
          // except for a theorem of a parent session, which this run never saw
          match self.g.verified.get(&i) {
            Some(v) => {
              let n_ofclass = v.n_ofclass;
              let mut d = Decoder::new(v);
              let stmt = self.decode_term(&mut d);
              let n = d.int();
              let var_map = (0..n)
                .map(|_| {
                  let a = self.decode_type(&mut d);
                  let b = self.decode_type(&mut d);
                  (a, b)
                })
                .collect();
              self.check_unconstrained(stmt, n_ofclass, var_map, &hyp_terms, shyps, hyps, concl);
            }
            None => assert!(
              self.g.external.contains(&i),
              "citation of theorem {i}, which this run did not check"
            ),
          }
          CProof { shyps, hyps, tpairs: TpairsId::EMPTY, concl }
        }
        (proof::Varify, &[args, p]) => {
          let mut subst = bp
            .parse_list(args)
            .map(|x| {
              let ((a, b), (c, d)) = self.parse(&mut m, bp, x);
              (a, b, self.alloc(Type::Var(c, d)))
            })
            .collect();
          let mut inst = Mapper::new(MapTypes::new(Varify::new(subst)));
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          // `varifyT_global'` varifies `attach_tpairs tpairs prop` as a whole, so that a
          // type variable shared between a flex-flex pair and the statement stays shared
          let n = self.ctx[tpairs].0.len();
          let prop = self.attach_tpairs(tpairs, concl);
          let prop = inst.apply(self, prop);
          let (tpairs, concl) = self.detach_tpairs(n, prop);
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::Weaken, &[a, sorts, p]) => {
          let a: TermId = self.parse(&mut m, bp, a);
          let TermData { ty, maxidx, .. } = self.ctx[a].1;
          assert!(ty == Ok(TypeId::PROP), "weaken: assumptions must have type prop");
          assert!(maxidx == MaxIdx::NONE, "weaken: assumptions may not contain variables");
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let mut hyps = self.ctx[hyps].0.clone();
          let h = self.hyp(a);
          hyps.insert(h);
          CProof { shyps: self.union(shyps, sorts), hyps: self.alloc(hyps), tpairs, concl }
        }
        (proof::LegacyFreezeT, &[p]) => {
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let n = self.ctx[tpairs].0.len();
          let prop = self.attach_tpairs(tpairs, concl);
          let subst = self.legacy_freeze_names(prop);
          let mut inst = Mapper::new(MapTypes::new(FreezeT { subst }));
          let prop = inst.apply(self, prop);
          let (tpairs, concl) = self.detach_tpairs(n, prop);
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::Lift, &[gprop, inc, sorts, p]) => {
          let gprop: TermId = self.parse(&mut m, bp, gprop);
          let inc: u32 = self.parse(&mut m, bp, inc);
          // `Thm.lift_rule` uses `inc = maxidx_of goal + 1`: `Logic.lift_all` splices the
          // goal's assumptions in verbatim while renaming the rule's variables, so anything
          // less would identify a rule variable with a different goal variable of the same
          // name
          assert!(inc + 1 > self.ctx[gprop].1.maxidx.0, "lift_rule: index not above the goal");
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          let CProof { mut shyps, hyps, tpairs, mut concl } = self.ctx[m.proofs[&p]].0;
          shyps = self.union(shyps, sorts);
          let mut lift = LiftVars::new(self, gprop, inc);
          let mut spine = vec![];
          while let Some((e1, e2)) = self.try_dest_imp(concl) {
            let f = self.dest_app(self.dest_app(concl).0).0;
            let e1 = lift.apply_spine(self, e1);
            spine.push(self.alloc(Term::App(f, e1)));
            concl = e2
          }
          concl = lift.apply_spine(self, concl);
          for &e in spine.iter().rev() {
            concl = self.alloc(Term::App(e, concl))
          }
          // `Logic.lift_abs` for the flex-flex pairs: the goal's parameters become `λ`s and
          // its assumptions are dropped, where `lift_all` keeps the whole skeleton
          let tpairs = self.map_tpairs(&mut |ck, t| lift.apply_abs(ck, t), tpairs);
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::IncrIndexes, &[inc, p]) => {
          let inc: u32 = self.parse(&mut m, bp, inc);
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let (tpairs, concl) = if inc == 0 {
            (tpairs, concl)
          } else {
            let mut inst = Mapper::new(IncrIdx::new(inc));
            let tpairs = self.map_tpairs(&mut |ck, t| inst.apply(ck, t), tpairs);
            (tpairs, inst.apply(self, concl))
          };
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::Assumption, &[env, i_, n_, p]) => {
          let env = Subst::from_env(&mut (&mut *self, &mut m), bp, env);
          let empty_env = env.tysubst.is_empty() && env.subst.is_empty();
          let sorts: Vec<_> = env.tysubst.iter().map(|&(_, _, ty)| ty).collect();
          let i: u32 = self.parse(&mut m, bp, i_);
          let n: u32 = self.parse(&mut m, bp, n_);
          let CProof { shyps, hyps, tpairs, concl: state } = self.ctx[m.proofs[&p]].0;
          let (bs, bi, c) = self.dest_state(state, i);
          let mut inst = Mapper::new(InstTerm::new(env, InstMode::Envir));
          self.check_env_sorts(&mut inst);
          // `Logic.assum_problems (~1, Bi)`: all of the subgoal's assumptions, closed over
          // its parameters, are candidates; the `n`-th one unifies with the conclusion.
          let mut params = vec![];
          let body = self.strip_all(bi, &mut params);
          let mut asms = vec![];
          let mut concl = body;
          while let Some((h, t)) = self.try_dest_imp(concl) {
            asms.push(h);
            concl = t
          }
          let asm = asms[n as usize - 1];
          let asm = self.close_params(&params, asm);
          let concl = self.close_params(&params, concl);
          let asm = inst.apply(self, asm);
          let concl = inst.apply(self, concl);
          let mut eta = EtaContract::new();
          let (asm, concl) = (eta.apply(self, asm), eta.apply(self, concl));
          cmp_site("assumption: assumption vs subgoal conclusion");
          Comparer::new(AConv).apply(self, asm, concl);
          // prop = `Logic.list_implies (Bs, C)`, normalised only if the unifier is non-trivial
          let mut prop = c;
          for &b in bs.iter().rev() {
            prop = self.mk_imp(b, prop)
          }
          let tpairs = if empty_env {
            tpairs
          } else {
            prop = inst.apply(self, prop);
            // `assumption` unifies `(close asm, concl') :: tpairs`, so the theorem's own
            // flex-flex pairs take part and the ones the unifier *solved* come back
            // trivial.  ML keeps the unifier's leftovers, which the trace does not record,
            // so drop the pairs that normalising made trivial.
            let tpairs = self.map_tpairs(&mut |ck, t| inst.apply(ck, t), tpairs);
            let l = self.ctx[tpairs].0.clone();
            let mut out = vec![];
            for &(a, b) in &l {
              if a != b && !self.aconv(a, b, &mut HashSet::new()) {
                out.push((a, b))
              }
            }
            self.alloc(out.into_boxed_slice())
          };
          // `Envir.insert_sorts` folds over the type env only
          let mut shyps = shyps;
          for ty in sorts {
            shyps = self.union(shyps, self.ctx[ty].1.sorts)
          }
          CProof { shyps, hyps, tpairs, concl: prop }
        }
        (proof::EqAssumption, &[i_, p]) => {
          let i: u32 = self.parse(&mut m, bp, i_);
          let CProof { shyps, hyps, tpairs, concl: state } = self.ctx[m.proofs[&p]].0;
          let (bs, bi, c) = self.dest_state(state, i);
          let mut params = vec![];
          let body = self.strip_all(bi, &mut params);
          let mut asms = vec![];
          let mut concl = body;
          while let Some((h, t)) = self.try_dest_imp(concl) {
            asms.push(h);
            concl = t
          }
          // `Envir.aeconv`: alpha equality up to beta/eta contraction
          let mut eta = EtaContract::new();
          let mut norm = BetaNorm::new();
          let goal = norm.apply(self, concl);
          let goal = eta.apply(self, goal);
          let found = asms.iter().any(|&a| {
            let a = norm.apply(self, a);
            let a = eta.apply(self, a);
            a == goal || self.aconv(a, goal, &mut HashSet::new())
          });
          assert!(found, "eq_assumption: no assumption matches the conclusion");
          let mut prop = c;
          for &b in bs.iter().rev() {
            prop = self.mk_imp(b, prop)
          }
          CProof { shyps, hyps, tpairs, concl: prop }
        }
        (proof::Rotate, &[m_, i_, p]) => {
          let rot = m_.as_int();
          let i: u32 = self.parse(&mut m, bp, i_);
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let mut bs = vec![];
          let mut st = concl;
          for _ in 0..i - 1 {
            let (h, t) = self.dest_imp(st);
            bs.push(h);
            st = t
          }
          let (bi, c) = self.dest_imp(st);
          let mut params = vec![];
          let rest = self.strip_all(bi, &mut params);
          let mut asms = vec![];
          let mut body = rest;
          while let Some((h, t)) = self.try_dest_imp(body) {
            asms.push(h);
            body = t
          }
          let n = asms.len() as i32;
          let bi = if rot == 0 || rot == n {
            bi
          } else {
            assert!(0 < rot && rot < n, "rotate_rule");
            let (ps, qs) = asms.split_at(rot as usize);
            let mut t = body;
            for &a in qs.iter().chain(ps).rev() {
              t = self.mk_imp(a, t)
            }
            for &(x, ty) in params.iter().rev() {
              t = self.mk_forall(x, ty, t)
            }
            t
          };
          let mut concl = self.mk_imp(bi, c);
          for &b in bs.iter().rev() {
            concl = self.mk_imp(b, concl)
          }
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::PermutePrems, &[j, k, p]) => {
          let j: u32 = self.parse(&mut m, bp, j);
          let k = k.as_int();
          let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&p]].0;
          let mut prems = vec![];
          let mut rest = concl;
          while let Some((h, t)) = self.try_dest_imp(rest) {
            prems.push(h);
            rest = t
          }
          let (fixed, moved) = prems.split_at(j as usize);
          let n_j = moved.len() as i32;
          let m2 = if k < 0 { n_j + k } else { k };
          let prems = if m2 == 0 || m2 == n_j {
            prems.clone()
          } else {
            assert!(0 < m2 && m2 < n_j, "permute_prems: k");
            let (ps, qs) = moved.split_at(m2 as usize);
            fixed.iter().chain(qs).chain(ps).copied().collect()
          };
          let mut concl = rest;
          for &a in prems.iter().rev() {
            concl = self.mk_imp(a, concl)
          }
          CProof { shyps, hyps, tpairs, concl }
        }
        (proof::Bicompose, &[args, p, q]) => {
          let args: BicomposeArgs = self.parse(&mut m, bp, args);
          let CProof { shyps: shyps1, hyps: hyps1, concl: rule, .. } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: state, .. } = self.ctx[m.proofs[&q]].0;

          // rule = ⟦rAs⟧ ⟹ B
          let mut b = rule;
          let mut r_as = vec![];
          for _ in 0..args.nsubgoal {
            let (h, t) = self.dest_imp(b);
            r_as.push(h);
            b = t
          }
          // state = ⟦Bs; Bi⟧ ⟹ C
          let (bs, bi, c) = self.dest_state(state, args.nbs + 1);

          if *DEBUG_BC {
            println!("  [bc] nbs={} nsubgoal={} flatten={} n={} nlift={} smax={} lifted={}",
              args.nbs, args.nsubgoal, args.flatten, args.n, args.nlift, args.smax,
              args.lifted);
            println!("       p(rule?)  = {:?}", self.pp(rule));
            println!("       q(state?) = {:?}", self.pp(state));
          }

          // `Envir.is_empty` / `Envir.above env smax` select how much of the result
          // `bicompose_aux` bothers to normalise, and the checker has to make the same
          // choice to reproduce the recorded statement exactly.  A `Vartab` is ordered by
          // index first (`Term_Ord.fast_indexname_ord`), so `Vartab.min` is the least
          // index assigned.
          let empty_env = args.env.tysubst.is_empty() && args.env.subst.is_empty();
          let above = (args.env.subst.iter().map(|e| e.0))
            .chain(args.env.tysubst.iter().map(|e| e.0))
            .all(|v| i64::from(self.ctx[v].0.1) > i64::from(args.smax));
          let mut inst = Mapper::new(InstTerm::new(args.env, InstMode::Envir));
          self.check_env_sorts(&mut inst);

          // the unifier is what justifies replacing the subgoal by the rule's premises;
          // when the rule was lifted, only the shortened disagreement pair was unified
          let bbi = if args.lifted { self.strip_assums2(b, bi) } else { (b, bi) };
          let b1 = inst.apply(self, bbi.0);
          let bi1 = inst.apply(self, bbi.1);
          let mut eta = EtaContract::new();
          let (b1, bi1) = (eta.apply(self, b1), eta.apply(self, bi1));
          if *DEBUG_BC {
            for &(v, vs, ty) in &inst.f.ty.f.subst.clone() {
              println!("  [bc] env tyvar {:?}:{:?} := {:?}", self.pp(v), self.pp(vs), self.pp(ty));
            }
            for &(v, vt, tm) in &inst.f.subst.clone() {
              println!("  [bc] env var {:?}:{:?} := {:?}", self.pp(v), self.pp(vt), self.pp(tm));
            }
            println!("  [bc] B  = {:?}", self.pp(b1));
            println!("  [bc] Bi = {:?}", self.pp(bi1));
          }
          // the unifier's leftovers, normalised and contracted like the rest, so that a
          // pair it declined to solve can excuse a difference here
          let mut tpairs_norm: Vec<(TermId, TermId)> = vec![];
          for &(a, b) in &args.tpairs {
            let (a, b) =
              if empty_env { (a, b) } else { (inst.apply(self, a), inst.apply(self, b)) };
            let (mut a, mut b) = (eta.apply(self, a), eta.apply(self, b));
            tpairs_norm.push((a, b));
            // a pair is recorded closed over the goal's parameters (`Logic.lift_abs`
            // abstracts where the statement quantifies), so the same disagreement appears
            // inside the statement with those `λ`s peeled off and the bounds still loose
            loop {
              let Term::Abs(_, ty1, e1) = self.ctx[a].0 else { break };
              let Term::Abs(_, ty2, e2) = self.ctx[b].0 else { break };
              if ty1 != ty2 {
                break
              }
              a = e1;
              b = e2;
              tpairs_norm.push((a, b))
            }
          }
          if *DEBUG_BC {
            for (a, b) in &tpairs_norm {
              println!("  [bc] tpair {:?}  ==?==  {:?}", self.pp(*a), self.pp(*b));
            }
          }
          cmp_site("bicompose: rule conclusion vs subgoal");
          Comparer::new(AConvModTpairs::new(tpairs_norm.clone())).apply(self, b1, bi1);

          // elim-resolution: the rule's first premise `A1` is discharged against `A1`'s own
          // `n`-th assumption, both closed over its parameters (`Logic.assum_problems`)
          let mut dpairs = vec![bbi];
          if args.n != 0 {
            let a1 = args.a_.expect("eresolution without a first premise");
            let mut params = vec![];
            let body = self.strip_all(a1, &mut params);
            let mut asms = vec![];
            let mut concl = body;
            for _ in 0..args.nlift {
              let Some((h, t)) = self.try_dest_imp(concl) else { break };
              asms.push(h);
              concl = t
            }
            let asm = asms[args.n as usize - 1];
            let asm = self.close_params(&params, asm);
            let concl = self.close_params(&params, concl);
            // `(concl', asm')` is a disagreement pair like `BBi`, so it feeds `rename_bvars`
            dpairs.push((concl, asm));
            let asm = inst.apply(self, asm);
            let concl = inst.apply(self, concl);
            let (asm, concl) = (eta.apply(self, asm), eta.apply(self, concl));
            cmp_site("eresolution: assumption vs the rule premise's conclusion");
            Comparer::new(AConvModTpairs::new(tpairs_norm.clone())).apply(self, asm, concl);
          }

          // Check the recorded new subgoals against the rule's own premises.  `newAs`
          // renames the rule's bound variables -- and some of its schematic variables -- to
          // the goal's parameter names (`rename_bvars`), strips off what lifting added
          // (`strip_apply`), and flattens the parameters of the premise that eresolution
          // consumed, so all of that has to be redone here to compare.
          let as0 = if args.n != 0 { &r_as[1..] } else { &r_as[..] };
          let as1 = match if args.lifted { self.rename_bvars(&dpairs, b, as0) } else { None } {
            Some(r) => {
              let mut ren = Mapper::new(r);
              as0.iter().map(|&a| self.strip_apply(&mut ren, b, a)).collect::<Vec<_>>()
            }
            None => as0.to_vec(),
          };
          assert!(as1.len() == args.as_.len(), "bicompose: wrong number of new subgoals");
          cmp_site("bicompose: recorded new subgoals vs the rule's premises");
          // `STRICT_AS=1` demands the recomputed `rename_bvars` renaming exactly, to
          // measure what the tolerant comparison is covering up
          let mut goal_vars = HashSet::new();
          self.add_var_names(bbi.1, &mut goal_vars);
          let mut cmp = Comparer::new(if *STRICT_AS {
            AConvModTpairs::new(tpairs_norm)
          } else {
            AConvModTpairs::modulo_renaming(tpairs_norm, goal_vars)
          });
          for (&x, &y) in as1.iter().zip(&args.as_) {
            let x = if args.flatten { self.flatten_params(args.n, x) } else { x };
            cmp.apply(self, x, y)
          }

          //
          // `addth` then does "minimal copying": with no unifier nothing is normalised at
          // all, and when the unifier assigns nothing below the state's maxidx the state's
          // own premises and conclusion are left as they stand.
          let mut concl;
          if empty_env {
            concl = c;
            for &a in args.as_.iter().rev() {
              concl = self.mk_imp(a, concl)
            }
          } else if above {
            concl = c;
            for i in (0..args.as_.len()).rev() {
              let a = args.as_[i];
              // `norm_term_skip env nlift`: the first `nlift` assumptions of a lifted
              // premise came from the goal, which the unifier does not touch
              let a = if args.lifted {
                self.norm_term_skip(&mut inst, args.nlift.saturating_sub(1), a)
              } else {
                inst.apply(self, a)
              };
              concl = self.mk_imp(a, concl)
            }
          } else {
            concl = inst.apply(self, c);
            for i in (0..args.as_.len()).rev() {
              let a = inst.apply(self, args.as_[i]);
              concl = self.mk_imp(a, concl)
            }
          }
          for &bj in bs.iter().rev() {
            let bj = if empty_env || above { bj } else { inst.apply(self, bj) };
            concl = self.mk_imp(bj, concl)
          }

          // `Envir.insert_sorts` folds over the *type* env only
          // (`Vartab.fold (Sorts.insert_typ o #2 o #2) o type_env`): the terms assigned by
          // the term env are already accounted for in the premises' own shyps.
          let mut shyps = self.union(shyps1, shyps2);
          for &(_, _, ty) in &inst.f.ty.f.subst {
            shyps = self.union(shyps, self.ctx[ty].1.sorts)
          }
          // the resulting flex-flex pairs are the unifier's leftovers, normalised like the
          // rest of the result; the premises' own tpairs were part of `dpairs`, so they are
          // subsumed rather than unioned in
          let tpairs: Vec<_> = (args.tpairs.iter())
            .map(|&(a, b)| {
              if empty_env {
                (a, b)
              } else {
                (inst.apply(self, a), inst.apply(self, b))
              }
            })
            .collect();
          let tpairs = self.alloc(tpairs.into_boxed_slice());
          CProof { shyps, hyps: self.union(hyps1, hyps2), tpairs, concl }
        }
        (tag, args) => panic!("unhandled rule {tag} with {} argument(s)", args.len()),
      };
      // println!(
      //   "{pf:?} => {:?}, {:?} |- {:?}",
      //   self.pp(pf2.shyps),
      //   self.pp(pf2.hyps),
      //   self.pp(pf2.concl)
      // );
      if *DEBUG_STEPS {
        println!("  rule {:2} shyps={:?} => {:?}", bp.get_enum(pf).0, self.pp(pf2.shyps),
          self.pp(pf2.concl));
      }
      if *DEBUG_RULES {
        RULE_COUNTS.with(|c| c.borrow_mut()[bp.get_enum(pf).0 as usize] += 1u64);
      }
      m.proofs.insert(pf, self.alloc(pf2));
    }
    let CProof { shyps, hyps, tpairs, concl } = self.ctx[m.proofs[&tr.root]].0;
    assert!(tpairs == TpairsId::EMPTY, "a stored theorem may not have flex-flex pairs");
    // println!(
    //   "want: {:?},\ngot: {:?}, {:?} |- {:?}",
    //   self.pp(prop),
    //   self.pp(shyps),
    //   self.pp(hyps),
    //   self.pp(concl)
    // );
    if tr.unconstrain_shyps < 0 {
      // a promise trace: `Thm.future`'s cterm fixed the statement and declared the sorts,
      // and there is no `unconstrainT` to reconcile -- so the statement must match as it
      // stands, sorts included, and the proof may not have picked up hypotheses
      assert!(
        hyps == HypsId::EMPTY && tr.unconstrain_hyps.is_empty(),
        "promise: the forked proof has hypotheses"
      );
      cmp_site("promise: the forked proof's statement vs the promised one");
      Comparer::new(AConv).apply(self, concl, prop);
    } else {
      self.check_unconstrained(
        prop,
        tr.unconstrain_shyps,
        tr.unconstrain_var_map.clone(),
        &tr.unconstrain_hyps,
        shyps,
        hyps,
        concl,
      );
    }
    let mut e = Encoder::default();
    self.encode(&mut e, prop, &tr.unconstrain_var_map, shyps);
    e.finish(tr.unconstrain_shyps)
  }

  /// The end of a theorem's check, shared with the citation rules: the statement the
  /// theorem is claimed to prove is `⟦OFCLASS(?'a, c); …; hyps⟧ ⟹ concl` with its type
  /// variables stripped of sorts, so peel the class premises off, check they cover the
  /// accumulated sort hypotheses, then discharge the hypotheses and compare.
  #[allow(clippy::too_many_arguments)]
  fn check_unconstrained(
    &mut self, mut prop: TermId, n_ofclass: i32, var_map: Vec<(TypeId, TypeId)>,
    unconstrain_hyps: &[TermId], shyps: SortsId, hyps: HypsId, concl: TermId,
  ) {
    let mut compare = Comparer::new(CompareTypes::new(StripSorts));
    let mut inst_var = Mapper::new(MapTypes::new(InstTVars::new(var_map)));
    let tr_unconstrain_shyps = n_ofclass.max(0) as u32;
    // a promise trace was never `unconstrainT`-ed: its sort hypotheses are declared by the
    // cterm `Thm.future` was given, and the *citing* proof checks them (`future_result`
    // requires `Sorts.subset (shyps, orig_shyps)`), so there is nothing to reconcile here
    if n_ofclass >= 0 && (tr_unconstrain_shyps != 0 || shyps != SortsId::EMPTY) {
      let mut classes = HashMap::<IndexNameId, IdxBitSet<ClassId>>::new();
      for _ in 0..tr_unconstrain_shyps {
        let (arg, rest) = self.dest_imp(prop);
        let (ty, cl) = self.dest_ofclass(arg);
        let (v, SortId::TOP) = self.dest_tvar(ty) else { panic!("unexpected sort") };
        classes.entry(v).or_default().insert(cl);
        prop = rest;
      }
      for &(_, to) in &inst_var.f.0.f.subst {
        let Type::Var(v, s) = self.ctx[to].0 else { panic!("expected var map") };
        if s != SortId::TOP {
          assert!(self.ctx[s].0.is_subset(&classes[&v]))
        }
      }
      let classes: BTreeSet<_> = classes.into_iter().map(|s| s.1).collect();
      for s in self.ctx[shyps].0.iter() {
        if s != SortId::TOP {
          let sc = &self.ctx[s].0;
          if !classes.iter().any(|c| sc.is_subset(c)) {
            println!("!! shyp not covered: {:?}", self.pp(s));
            println!("   unconstrain_shyps = {tr_unconstrain_shyps}");
            println!("   classes = {:?}",
              classes.iter().map(|c| c.iter().map(|c| self.pp(c)).collect::<Vec<_>>())
                .collect::<Vec<_>>());
            println!("   all shyps = {:?}", self.pp(shyps));
          }
          assert!(classes.iter().any(|c| sc.is_subset(c)))
        }
      }
    }
    if hyps != HypsId::EMPTY || !unconstrain_hyps.is_empty() {
      let mut hyps = self.ctx[hyps].0.clone();
      for &h in unconstrain_hyps {
        hyps.remove(self.hyp(h));
        let (arg, rest) = self.dest_imp(prop);
        let h = inst_var.apply(self, h);
        if *DEBUG_FINAL {
          println!("=== hyp check\n  got  = {:?}\n  want = {:?}", self.pp(h), self.pp(arg));
        }
        cmp_site("theorem: recorded hypothesis vs the statement's premise");
        compare.apply(self, h, arg);
        prop = rest;
      }
      assert!(hyps.is_empty());
    }
    let concl = inst_var.apply(self, concl);
    if *DEBUG_FINAL {
      println!("=== final check");
      println!("  got  = {:?}", self.pp(concl));
      println!("  want = {:?}", self.pp(prop));
    }
    compare.apply(self, concl, prop);
  }
}

struct Mapper<I, F> {
  f: F,
  map: HashMap<I, I>,
}
trait Map<I>: Sized {
  fn easy(_: &mut Mapper<I, Self>, _: &mut Checker<'_>, _: I) -> Option<I> {
    None
  }
  fn apply(_: &mut Mapper<I, Self>, _: &mut Checker<'_>, t: I) -> I {
    t
  }
}

impl<I: Idx, F: Map<I>> Mapper<I, F> {
  fn new(f: F) -> Self {
    Self { f, map: HashMap::new() }
  }
  fn apply(&mut self, ck: &mut Checker<'_>, t: I) -> I {
    if let Some(t2) = F::easy(self, ck, t) {
      return t2;
    }
    if let Some(&t2) = self.map.get(&t) {
      return t2;
    }
    let t2 = F::apply(self, ck, t);
    self.map.insert(t, t2);
    t2
  }
}
impl<F: Map<TermId>> Mapper<TermId, F> {
  fn apply_hyp(&mut self, ck: &mut Checker<'_>, h: HypId) -> HypId {
    let t = ck.ctx[h].0;
    let t2 = self.apply(ck, ck.ctx[h].0);
    if t == t2 {
      h
    } else {
      ck.hyp(t2)
    }
  }
  fn apply_hyps(&mut self, ck: &mut Checker<'_>, hs: HypsId) -> HypsId {
    if hs == HypsId::EMPTY {
      return hs;
    }
    let mut hs2 = IdxBitSet::new();
    for h in ck.ctx[hs].0.clone().iter() {
      hs2.insert(self.apply_hyp(ck, h));
    }
    ck.alloc(hs2)
  }
}

/// Rename every `Abs` binder to one canonical name, so that hash-consing identifies
/// alpha-variants (see [`Checker::hyp`])
struct CanonBinders;
impl Map<TermId> for CanonBinders {
  fn apply(map: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> TermId {
    match ck.ctx[t].0 {
      Term::Abs(_, ty, e) => {
        let e = map.apply(ck, e);
        let x = ck.alloc("_");
        ck.alloc(Term::Abs(x, ty, e))
      }
      Term::App(f, u) => {
        let f = map.apply(ck, f);
        let u = map.apply(ck, u);
        ck.alloc(Term::App(f, u))
      }
      _ => t,
    }
  }
}

/// the renaming computed by [`Checker::rename_bvars`]: schematic variable base names and
/// `Abs` binder names
struct RenameBvars {
  vars: HashMap<StringId, StringId>,
  bounds: HashMap<StringId, StringId>,
}
impl Map<TermId> for RenameBvars {
  fn apply(map: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> TermId {
    match ck.ctx[t].0 {
      Term::Var(x, ty) => {
        let (name, i) = ck.ctx[x].0;
        match map.f.vars.get(&name) {
          Some(&y) if y != name => {
            let x = ck.alloc((y, i));
            ck.alloc(Term::Var(x, ty))
          }
          _ => t,
        }
      }
      Term::Abs(x, ty, b) => {
        let b = map.apply(ck, b);
        let x = map.f.bounds.get(&x).copied().unwrap_or(x);
        ck.alloc(Term::Abs(x, ty, b))
      }
      Term::App(f, u) => {
        let f = map.apply(ck, f);
        let u = map.apply(ck, u);
        ck.alloc(Term::App(f, u))
      }
      _ => t,
    }
  }
}

/// the sort a constant's declaration gives one of its type arguments
fn decl_var_sort(decl: &crate::Type, x: &str) -> Option<Vec<String>> {
  match decl {
    crate::Type::Free(y, s) | crate::Type::Var(y, _, s) if y == x => Some(s.clone()),
    crate::Type::Type(_, args) => args.iter().find_map(|a| decl_var_sort(a, x)),
    _ => None,
  }
}

/// `Symbol.bump_string`: `x` → `xa` → `xb` … → `xz` → `xaa`, with the carry going right
/// to left over the trailing alphabetic run
fn bump_string(s: &str) -> String {
  let mut cs: Vec<char> = s.chars().collect();
  let mut i = cs.len();
  loop {
    if i == 0 {
      cs.insert(0, 'a');
      break
    }
    i -= 1;
    match cs[i] {
      'z' => cs[i] = 'a',
      c if c.is_ascii_lowercase() => {
        cs[i] = (c as u8 + 1) as char;
        break
      }
      _ => {
        cs.insert(i + 1, 'a');
        break
      }
    }
  }
  cs.into_iter().collect()
}

/// `Name.variant`: `x` if it is free, else `xa`, `xb`, … until one is
fn variant_name(base: &str, used: &[String]) -> String {
  // `Name.clean_index`: trailing underscores are re-attached at the end
  let clean = base.trim_end_matches('_');
  let n = base.len() - clean.len();
  let mut x = clean.to_owned();
  if used.iter().any(|u| *u == x) {
    x = format!("{x}a");
    while used.iter().any(|u| *u == x) {
      x = bump_string(&x)
    }
  }
  x + &"_".repeat(n)
}

/// `Type.legacy_freeze`'s type operation: each `TVar` becomes the `TFree` chosen for it
struct FreezeT {
  subst: HashMap<IndexNameId, StringId>,
}
impl Map<TypeId> for FreezeT {
  fn easy(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> Option<TypeId> {
    Some(match ck.ctx[t].0 {
      Type::Var(x, s) => match inst.f.subst.get(&x) {
        Some(&a) => ck.alloc(Type::Free(a, s)),
        None => t,
      },
      Type::Free(..) => t,
      _ => return None,
    })
  }
  fn apply(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> TypeId {
    let Type::Type(c, tys) = ck.ctx[t].0 else { unreachable!() };
    let tys = tys.iter().map(|&t| inst.apply(ck, t)).collect::<Vec<_>>();
    ck.alloc_copy(&Type::Type(c, &tys))
  }
}

/// writes the flat encoding of [`VerifiedThm`]
#[derive(Default)]
pub struct Encoder {
  strings: Vec<String>,
  map: HashMap<StringId, u32>,
  /// terms and types are hash-consed, and a statement is a DAG with a lot of sharing --
  /// writing it out as a tree is what blew memory up before.  A node already written is
  /// emitted as a back-reference to its index.
  terms: HashMap<TermId, u32>,
  types: HashMap<TypeId, u32>,
  buf: Vec<u8>,
}
impl Encoder {
  pub fn finish(self, n_ofclass: i32) -> VerifiedThm {
    VerifiedThm { strings: self.strings, buf: self.buf, n_ofclass }
  }

  fn int(&mut self, mut n: u32) {
    loop {
      let b = (n & 0x7f) as u8;
      n >>= 7;
      if n == 0 {
        return self.buf.push(b)
      }
      self.buf.push(b | 0x80)
    }
  }

  fn str(&mut self, ck: &Checker<'_>, s: StringId) {
    let i = *self.map.entry(s).or_insert_with(|| {
      self.strings.push(ck.ctx.strings.0[s].0.to_string());
      self.strings.len() as u32 - 1
    });
    self.int(i)
  }

  fn sort(&mut self, ck: &Checker<'_>, s: SortId) {
    let cs = ck.ctx[s].0.iter().collect::<Vec<_>>();
    self.int(cs.len() as u32);
    for c in cs {
      self.str(ck, ck.ctx[c].0)
    }
  }

  fn ty(&mut self, ck: &Checker<'_>, t: TypeId) {
    if let Some(&i) = self.types.get(&t) {
      self.buf.push(3);
      return self.int(i)
    }
    self.ty_inner(ck, t);
    let n = self.types.len() as u32;
    self.types.insert(t, n);
  }

  fn ty_inner(&mut self, ck: &Checker<'_>, t: TypeId) {
    match ck.ctx[t].0 {
      Type::Type(c, tys) => {
        self.buf.push(0);
        self.str(ck, c);
        self.int(tys.len() as u32);
        for &t in tys {
          self.ty(ck, t)
        }
      }
      Type::Free(x, s) => {
        self.buf.push(1);
        self.str(ck, x);
        self.sort(ck, s)
      }
      Type::Var(x, s) => {
        self.buf.push(2);
        let (x, i) = ck.ctx[x].0;
        self.str(ck, x);
        self.int(i);
        self.sort(ck, s)
      }
    }
  }

  fn term(&mut self, ck: &Checker<'_>, t: TermId) {
    if let Some(&i) = self.terms.get(&t) {
      self.buf.push(6);
      return self.int(i)
    }
    self.term_inner(ck, t);
    let n = self.terms.len() as u32;
    self.terms.insert(t, n);
  }

  fn term_inner(&mut self, ck: &Checker<'_>, t: TermId) {
    match ck.ctx[t].0 {
      Term::Const(c, ty) => {
        self.buf.push(0);
        self.str(ck, c);
        self.ty(ck, ty)
      }
      Term::Free(x, ty) => {
        self.buf.push(1);
        self.str(ck, x);
        self.ty(ck, ty)
      }
      Term::Var(x, ty) => {
        self.buf.push(2);
        let (x, i) = ck.ctx[x].0;
        self.str(ck, x);
        self.int(i);
        self.ty(ck, ty)
      }
      Term::Bound(i) => {
        self.buf.push(3);
        self.int(i)
      }
      Term::Abs(x, ty, e) => {
        self.buf.push(4);
        self.str(ck, x);
        self.ty(ck, ty);
        self.term(ck, e)
      }
      Term::App(f, u) => {
        self.buf.push(5);
        self.term(ck, f);
        self.term(ck, u)
      }
    }
  }
}

/// reads it back
struct Decoder<'a> {
  v: &'a VerifiedThm,
  pos: usize,
  terms: Vec<TermId>,
  types: Vec<TypeId>,
}
impl<'a> Decoder<'a> {
  fn new(v: &'a VerifiedThm) -> Self {
    Self { v, pos: 0, terms: vec![], types: vec![] }
  }
}
impl Decoder<'_> {
  fn peek(&self) -> u8 {
    self.v.buf[self.pos]
  }

  fn byte(&mut self) -> u8 {
    let b = self.v.buf[self.pos];
    self.pos += 1;
    b
  }

  fn int(&mut self) -> u32 {
    let mut n = 0;
    let mut shift = 0;
    loop {
      let b = self.byte();
      n |= u32::from(b & 0x7f) << shift;
      if b & 0x80 == 0 {
        return n
      }
      shift += 7
    }
  }

  fn str(&mut self, ck: &mut Checker<'_>) -> StringId {
    let i = self.int();
    ck.alloc_copy(&&*self.v.strings[i as usize])
  }
}

struct MapTypes<T>(Mapper<TypeId, T>);

impl<T: Map<TypeId>> MapTypes<T> {
  fn new(f: T) -> Self {
    Self(Mapper::new(f))
  }
}
impl<T: Map<TypeId>> Map<TermId> for MapTypes<T> {
  fn easy(_: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> Option<TermId> {
    if matches!(ck.ctx[t].0, Term::Bound(_)) {
      Some(t)
    } else {
      None
    }
  }
  fn apply(subst: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> TermId {
    match ck.ctx[t].0 {
      Term::Const(c, ty) => {
        let ty2 = subst.f.0.apply(ck, ty);
        ck.alloc(Term::Const(c, ty2))
      }
      Term::Free(x, ty) => {
        let ty2 = subst.f.0.apply(ck, ty);
        ck.alloc(Term::Free(x, ty2))
      }
      Term::Var(x, ty) => {
        let ty2 = subst.f.0.apply(ck, ty);
        ck.alloc(Term::Var(x, ty2))
      }
      Term::Abs(x, ty, e) => {
        let ty2 = subst.f.0.apply(ck, ty);
        let e2 = subst.apply(ck, e);
        ck.alloc(Term::Abs(x, ty2, e2))
      }
      Term::App(t, u) => {
        let t2 = subst.apply(ck, t);
        let u2 = subst.apply(ck, u);
        ck.alloc(Term::App(t2, u2))
      }
      Term::Bound(_) => unreachable!(),
    }
  }
}

struct InstTVars {
  subst: Vec<(TypeId, TypeId)>,
}
impl InstTVars {
  fn new(mut subst: Vec<(TypeId, TypeId)>) -> Self {
    subst.sort_by_key(|x| x.0);
    Self { subst }
  }
}
impl Map<TypeId> for InstTVars {
  fn easy(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> Option<TypeId> {
    Some(match ck.ctx[t].0 {
      Type::Free(..) | Type::Var(..) => {
        let j = inst.f.subst.binary_search_by_key(&t, |x| x.0).unwrap();
        inst.f.subst[j].1
      }
      _ => return None,
    })
  }
  fn apply(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> TypeId {
    let Type::Type(c, tys) = ck.ctx[t].0 else { unreachable!() };
    let tys = tys.iter().map(|&t| inst.apply(ck, t)).collect::<Vec<_>>();
    ck.alloc_copy(&Type::Type(c, &tys))
  }
}

struct InstType {
  subst: Box<[(IndexNameId, SortId, TypeId)]>,
  /// `Envir.norm_type` renormalises what it substitutes (`Same.commit norm U`), since a
  /// unifier's `tyenv` need not be idempotent -- unification of `'a.3` with `'a.1` with
  /// `'b.1` leaves the chain in place.  `Term_Subst.instantiateT` does not.
  chain: bool,
}
impl InstType {
  fn new(mut subst: Box<[(IndexNameId, SortId, TypeId)]>, chain: bool) -> Self {
    subst.sort_by_key(|x| (x.0, x.1));
    Self { subst, chain }
  }
}
impl Map<TypeId> for InstType {
  fn easy(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> Option<TypeId> {
    if inst.f.subst.is_empty() {
      return Some(t);
    }
    Some(match ck.ctx[t].0 {
      Type::Free(..) => t,
      Type::Var(i, s) => match inst.f.subst.binary_search_by_key(&(i, s), |x| (x.0, x.1)) {
        Ok(j) => {
          let u = inst.f.subst[j].2;
          if inst.f.chain {
            return Some(inst.apply(ck, u))
          }
          u
        }
        _ => t,
      },
      _ => return None,
    })
  }
  fn apply(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> TypeId {
    let Type::Type(c, tys) = ck.ctx[t].0 else { unreachable!() };
    let tys = tys.iter().map(|&t| inst.apply(ck, t)).collect::<Vec<_>>();
    ck.alloc_copy(&Type::Type(c, &tys))
  }
}

/// Which of the three substitution operations the ML side used: they differ only in how
/// much β-reduction they do, but the checker has to match it exactly.
#[derive(Clone, Copy, PartialEq, Eq)]
enum InstMode {
  /// `Term_Subst.instantiate`: substitute and stop, redexes and all
  Inst,
  /// `Term_Subst.instantiate_beta`: reduce only the redexes the substitution itself
  /// creates, at the head of an application spine (`Term.betapplys`), without
  /// renormalising the result.  This is what `\<^instantiate>` uses by default.
  InstBeta,
  /// `Envir.norm_term`: a full β-normaliser that also renormalises substituted terms,
  /// since a unifier need not be idempotent
  Envir,
}

struct InstTerm {
  ty: Mapper<TypeId, InstType>,
  subst: Box<[(IndexNameId, TypeId, TermId)]>,
  mode: InstMode,
}
impl InstTerm {
  fn new(mut subst: Subst, mode: InstMode) -> Self {
    let ty = Mapper::new(InstType::new(subst.tysubst, mode == InstMode::Envir));
    // an Envir is keyed by indexname alone, an instantiation by (indexname, type)
    subst.subst.sort_by_key(|x| (x.0, x.1));
    Self { ty, subst: subst.subst, mode }
  }

  /// `Term.betapplys`: apply, reducing each redex as it appears, and no further
  fn betapplys(ck: &mut Checker<'_>, mut u: TermId, args: &[TermId]) -> TermId {
    for &a in args {
      u = match ck.ctx[u].0 {
        Term::Abs(_, _, b) => SubstBound::new(&[a]).apply(ck, b, 0),
        _ => ck.alloc(Term::App(u, a)),
      }
    }
    u
  }
}

impl Map<TermId> for InstTerm {
  fn easy(_: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> Option<TermId> {
    if matches!(ck.ctx[t].0, Term::Bound(_)) {
      Some(t)
    } else {
      None
    }
  }
  fn apply(inst: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> TermId {
    match ck.ctx[t].0 {
      Term::Const(c, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        ck.alloc(Term::Const(c, ty2))
      }
      Term::Free(x, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        ck.alloc(Term::Free(x, ty2))
      }
      Term::Var(x, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        if inst.f.mode == InstMode::Envir {
          // An Envir's tenv is a Vartab: keyed by indexname alone, with the type in the
          // value and matched by `Type.unified tyenv` -- i.e. modulo the type substitution
          // (`lookup = lookup_check (Type.unified tyenv) tenv`).  Keying on the pair is
          // over-specific and misses whenever the occurrence's type has been instantiated.
          if let Ok(j) = inst.f.subst.binary_search_by_key(&x, |e| e.0) {
            let (_, vt, t) = inst.f.subst[j];
            let vt = inst.f.ty.apply(ck, vt);
            if vt == ty2 {
              // and unlike Term_Subst.instantiate, norm_term renormalises the result,
              // since a unifier need not be idempotent
              return inst.apply(ck, t);
            }
          }
          ck.alloc(Term::Var(x, ty2))
        } else {
          // Thm.instantiate's Vars.table is keyed by (indexname, instantiated type), and
          // inserts the term as it stands
          match inst.f.subst.binary_search_by_key(&(x, ty2), |e| (e.0, e.1)) {
            Ok(j) => inst.f.subst[j].2,
            _ => ck.alloc(Term::Var(x, ty2)),
          }
        }
      }
      Term::Abs(x, ty, e) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        let e2 = inst.apply(ck, e);
        ck.alloc(Term::Abs(x, ty2, e2))
      }
      Term::App(t, u) => match inst.f.mode {
        InstMode::Envir => {
          if let Term::Abs(_, _, b) = ck.ctx[t].0 {
            let t2 = SubstBound::new(&[u]).apply(ck, b, 0);
            return inst.apply(ck, t2);
          }
          let t2 = inst.apply(ck, t);
          if let Term::Abs(_, _, b) = ck.ctx[t2].0 {
            let t2 = SubstBound::new(&[u]).apply(ck, b, 0);
            return inst.apply(ck, t2);
          }
          let u2 = inst.apply(ck, u);
          ck.alloc(Term::App(t2, u2))
        }
        InstMode::Inst => {
          let t2 = inst.apply(ck, t);
          let u2 = inst.apply(ck, u);
          ck.alloc(Term::App(t2, u2))
        }
        // `inst_beta_same` dispatches on the *head* of the spine: only a head variable
        // whose replacement is a lambda gets reduced, against the substituted arguments.
        InstMode::InstBeta => {
          let mut args = vec![u];
          let mut head = t;
          while let Term::App(f, a) = ck.ctx[head].0 {
            args.push(a);
            head = f
          }
          args.reverse();
          for a in &mut args {
            *a = inst.apply(ck, *a)
          }
          if let Term::Var(x, ty) = ck.ctx[head].0 {
            let ty2 = inst.f.ty.apply(ck, ty);
            let h = match inst.f.subst.binary_search_by_key(&(x, ty2), |e| (e.0, e.1)) {
              Ok(j) => inst.f.subst[j].2,
              _ => ck.alloc(Term::Var(x, ty2)),
            };
            return Self::betapplys(ck, h, &args)
          }
          let mut h = inst.apply(ck, head);
          for &a in &args {
            h = ck.alloc(Term::App(h, a))
          }
          h
        }
      },
      Term::Bound(_) => unreachable!(),
    }
  }
}

struct GenType {
  frees: Vec<StringId>,
  idx: u32,
}
impl GenType {
  fn new(mut frees: Vec<StringId>, idx: u32) -> Self {
    frees.sort();
    Self { frees, idx }
  }
}
impl Map<TypeId> for GenType {
  fn easy(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> Option<TypeId> {
    Some(match ck.ctx[t].0 {
      Type::Free(x, s) => {
        if inst.f.frees.binary_search(&x).is_ok() {
          let x = ck.alloc((x, inst.f.idx));
          ck.alloc(Type::Var(x, s))
        } else {
          ck.alloc(Type::Free(x, s))
        }
      }
      Type::Var(..) => t,
      _ => return None,
    })
  }
  fn apply(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> TypeId {
    let Type::Type(c, tys) = ck.ctx[t].0 else { unreachable!() };
    let tys = tys.iter().map(|&t| inst.apply(ck, t)).collect::<Vec<_>>();
    ck.alloc_copy(&Type::Type(c, &tys))
  }
}

struct GenTerm {
  ty: Mapper<TypeId, GenType>,
  frees: Vec<StringId>,
}
impl GenTerm {
  fn new(tfrees: Vec<StringId>, mut frees: Vec<StringId>, idx: u32) -> Self {
    let ty = Mapper::new(GenType::new(tfrees, idx));
    frees.sort();
    Self { ty, frees }
  }
}

impl Map<TermId> for GenTerm {
  fn easy(_: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> Option<TermId> {
    if matches!(ck.ctx[t].0, Term::Bound(_)) {
      Some(t)
    } else {
      None
    }
  }
  fn apply(inst: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> TermId {
    match ck.ctx[t].0 {
      Term::Const(c, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        ck.alloc(Term::Const(c, ty2))
      }
      Term::Free(x, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        if inst.f.frees.binary_search(&x).is_ok() {
          let x = ck.clean_index(x, inst.f.ty.f.idx);
          ck.alloc(Term::Var(x, ty2))
        } else {
          ck.alloc(Term::Free(x, ty2))
        }
      }
      Term::Var(x, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        ck.alloc(Term::Var(x, ty2))
      }
      Term::Abs(x, ty, e) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        let e2 = inst.apply(ck, e);
        ck.alloc(Term::Abs(x, ty2, e2))
      }
      Term::App(t, u) => {
        let t2 = inst.apply(ck, t);
        let u2 = inst.apply(ck, u);
        ck.alloc(Term::App(t2, u2))
      }
      Term::Bound(_) => unreachable!(),
    }
  }
}

struct IncrBound {
  map: HashMap<(TermId, u32, u32), TermId>,
}
impl IncrBound {
  fn new() -> Self {
    Self { map: HashMap::new() }
  }
}

impl IncrBound {
  fn apply0(&mut self, ck: &mut Checker<'_>, t: TermId, inc: u32) -> TermId {
    if inc == 0 {
      t
    } else {
      self.apply(ck, t, inc, 0)
    }
  }

  fn apply(&mut self, ck: &mut Checker<'_>, t: TermId, inc: u32, depth: u32) -> TermId {
    if let Some(&t) = self.map.get(&(t, inc, depth)) {
      return t;
    }
    let ret = match ck.ctx[t].0 {
      Term::Abs(x, ty, e) => {
        let e2 = self.apply(ck, e, inc, depth + 1);
        ck.alloc(Term::Abs(x, ty, e2))
      }
      Term::App(t, u) => {
        let t2 = self.apply(ck, t, inc, depth);
        let u2 = self.apply(ck, u, inc, depth);
        ck.alloc(Term::App(t2, u2))
      }
      Term::Bound(i) if i >= depth => ck.alloc(Term::Bound(i + inc)),
      _ => t,
    };
    self.map.insert((t, inc, depth), ret);
    ret
  }
}

/// `Term.abstract_over`: replace a variable by the bound variable of a new abstraction.
/// `Envir.beta_norm`: full beta normal form.
struct BetaNorm {
  map: HashMap<TermId, TermId>,
}
impl BetaNorm {
  fn new() -> Self {
    Self { map: HashMap::new() }
  }

  fn apply(&mut self, ck: &mut Checker<'_>, t: TermId) -> TermId {
    if let Some(&t) = self.map.get(&t) {
      return t;
    }
    let ret = match ck.ctx[t].0 {
      Term::Abs(x, ty, e) => {
        let e = self.apply(ck, e);
        ck.alloc(Term::Abs(x, ty, e))
      }
      Term::App(f, u) => {
        let f = self.apply(ck, f);
        if let Term::Abs(_, _, b) = ck.ctx[f].0 {
          let t = SubstBound::new(&[u]).apply(ck, b, 0);
          self.apply(ck, t)
        } else {
          let u = self.apply(ck, u);
          ck.alloc(Term::App(f, u))
        }
      }
      _ => t,
    };
    self.map.insert(t, ret);
    ret
  }
}

/// `Envir.eta_contract`: bottom-up, replacing `Abs (a, T, f $ Bound 0)` by `f` whenever `f`
/// has no loose `Bound 0` (`Term.is_dependent`).
struct EtaContract {
  map: HashMap<TermId, TermId>,
}
impl EtaContract {
  fn new() -> Self {
    Self { map: HashMap::new() }
  }

  fn apply(&mut self, ck: &mut Checker<'_>, t: TermId) -> TermId {
    if let Some(&t) = self.map.get(&t) {
      return t;
    }
    let ret = match ck.ctx[t].0 {
      Term::Abs(x, ty, body) => {
        let body = self.apply(ck, body);
        match ck.ctx[body].0 {
          Term::App(f, arg)
            if matches!(ck.ctx[arg].0, Term::Bound(0)) && !ck.loose_bvar1(f, 0) =>
          {
            ck.decr_bound(f, 0)
          }
          _ => ck.alloc(Term::Abs(x, ty, body)),
        }
      }
      Term::App(f, u) => {
        let f = self.apply(ck, f);
        let u = self.apply(ck, u);
        ck.alloc(Term::App(f, u))
      }
      _ => t,
    };
    self.map.insert(t, ret);
    ret
  }
}

struct AbstractOver {
  x: TermId,
  map: HashMap<(TermId, u32), TermId>,
}
impl AbstractOver {
  fn new(x: TermId) -> Self {
    Self { x, map: HashMap::new() }
  }

  fn apply(&mut self, ck: &mut Checker<'_>, t: TermId, depth: u32) -> TermId {
    if t == self.x {
      return ck.alloc(Term::Bound(depth));
    }
    if let Some(&t) = self.map.get(&(t, depth)) {
      return t;
    }
    let ret = match ck.ctx[t].0 {
      Term::Abs(x, ty, e) => {
        let e = self.apply(ck, e, depth + 1);
        ck.alloc(Term::Abs(x, ty, e))
      }
      Term::App(f, a) => {
        let f = self.apply(ck, f, depth);
        let a = self.apply(ck, a, depth);
        ck.alloc(Term::App(f, a))
      }
      _ => t,
    };
    self.map.insert((t, depth), ret);
    ret
  }
}

struct SubstBound<'a> {
  subst: &'a [TermId],
  inc: IncrBound,
  map: HashMap<(TermId, u32), TermId>,
}
impl<'a> SubstBound<'a> {
  fn new(subst: &'a [TermId]) -> Self {
    Self { subst, inc: IncrBound::new(), map: HashMap::new() }
  }
}

impl SubstBound<'_> {
  fn apply(&mut self, ck: &mut Checker<'_>, t: TermId, depth: u32) -> TermId {
    if let Some(&t) = self.map.get(&(t, depth)) {
      return t;
    }
    let ret = match ck.ctx[t].0 {
      Term::Abs(x, ty, e) => {
        let e2 = self.apply(ck, e, depth + 1);
        ck.alloc(Term::Abs(x, ty, e2))
      }
      Term::App(t, u) => {
        let t2 = self.apply(ck, t, depth);
        let u2 = self.apply(ck, u, depth);
        ck.alloc(Term::App(t2, u2))
      }
      Term::Bound(i) if i >= depth => {
        if let Some(&t) = self.subst.get((i - depth) as usize) {
          self.inc.apply0(ck, t, depth)
        } else {
          ck.alloc(Term::Bound(i - self.subst.len() as u32))
        }
      }
      _ => t,
    };
    self.map.insert((t, depth), ret);
    ret
  }
}

struct LiftVarsT {
  inc: u32,
}
impl Map<TypeId> for LiftVarsT {
  fn easy(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> Option<TypeId> {
    Some(match ck.ctx[t].0 {
      Type::Var(x, s) => {
        let (x, i) = ck.ctx[x].0;
        let x = ck.alloc((x, i + inst.f.inc));
        ck.alloc(Type::Var(x, s))
      }
      Type::Free(..) => t,
      _ if ck.ctx[t].1.maxidx == MaxIdx::NONE => t,
      _ => return None,
    })
  }
  fn apply(inst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> TypeId {
    let Type::Type(c, tys) = ck.ctx[t].0 else { unreachable!() };
    let tys = tys.iter().map(|&t| inst.apply(ck, t)).collect::<Vec<_>>();
    ck.alloc_copy(&Type::Type(c, &tys))
  }
}

/// `Logic.incr_indexes ([], inc)`: raise the index of every schematic variable, in terms
/// and in the types inside them.
struct IncrIdx {
  ty: Mapper<TypeId, LiftVarsT>,
  inc: u32,
}
impl IncrIdx {
  fn new(inc: u32) -> Self {
    Self { ty: Mapper::new(LiftVarsT { inc }), inc }
  }
}
impl Map<TermId> for IncrIdx {
  fn easy(_: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> Option<TermId> {
    if matches!(ck.ctx[t].0, Term::Bound(_)) {
      Some(t)
    } else {
      None
    }
  }
  fn apply(inst: &mut Mapper<TermId, Self>, ck: &mut Checker<'_>, t: TermId) -> TermId {
    match ck.ctx[t].0 {
      Term::Const(c, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        ck.alloc(Term::Const(c, ty2))
      }
      Term::Free(x, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        ck.alloc(Term::Free(x, ty2))
      }
      Term::Var(x, ty) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        let (name, i) = ck.ctx[x].0;
        let x2 = ck.alloc((name, i + inst.f.inc));
        ck.alloc(Term::Var(x2, ty2))
      }
      Term::Abs(x, ty, e) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        let e2 = inst.apply(ck, e);
        ck.alloc(Term::Abs(x, ty2, e2))
      }
      Term::App(t, u) => {
        let t2 = inst.apply(ck, t);
        let u2 = inst.apply(ck, u);
        ck.alloc(Term::App(t2, u2))
      }
      Term::Bound(_) => unreachable!(),
    }
  }
}

struct LiftVars {
  spine: Vec<TermId>,
  tys: Vec<TypeId>,
  lift: Mapper<TypeId, LiftVarsT>,
  map: HashMap<(TermId, u32), TermId>,
}
impl LiftVars {
  fn new(ck: &Checker<'_>, mut gprop: TermId, inc: u32) -> Self {
    let mut spine = vec![];
    let mut tys = vec![];
    loop {
      if let Some((_, e2)) = ck.try_dest_imp(gprop) {
        spine.push(gprop);
        gprop = e2
      } else {
        let Some((_, e)) = ck.try_dest_forall(gprop) else { break };
        let Term::Abs(_, ty, b) = ck.ctx[e].0 else { break };
        spine.push(gprop);
        tys.push(ty);
        gprop = b
      }
    }
    Self { spine, tys, lift: Mapper::new(LiftVarsT { inc }), map: HashMap::new() }
  }
}

impl LiftVars {
  /// `Logic.lift_abs`: like `lift_all`, but the goal's parameters become `λ`-binders and
  /// its assumptions are dropped -- flex-flex pairs are terms, not propositions
  fn apply_abs(&mut self, ck: &mut Checker<'_>, t: TermId) -> TermId {
    let mut t2 = self.apply(ck, t, 0);
    for &s in self.spine.clone().iter().rev() {
      let (f, e2) = ck.dest_app(s);
      if let Term::Const(..) = ck.ctx[f].0 {
        let Term::Abs(x, ty, _) = ck.ctx[e2].0 else { unreachable!() };
        t2 = ck.alloc(Term::Abs(x, ty, t2))
      }
    }
    t2
  }

  fn apply_spine(&mut self, ck: &mut Checker<'_>, t: TermId) -> TermId {
    let mut t2 = self.apply(ck, t, 0);
    for &t in self.spine.iter().rev() {
      let (f, e2) = ck.dest_app(t);
      match ck.ctx[f].0 {
        Term::Const(..) => {
          let Term::Abs(x, ty, _) = ck.ctx[e2].0 else { unreachable!() };
          let t = ck.alloc(Term::Abs(x, ty, t2));
          t2 = ck.alloc(Term::App(f, t));
        }
        Term::App(..) => t2 = ck.alloc(Term::App(f, t2)),
        _ => unreachable!(),
      }
    }
    t2
  }

  fn apply(&mut self, ck: &mut Checker<'_>, t: TermId, depth: u32) -> TermId {
    if let Some(&t) = self.map.get(&(t, depth)) {
      return t;
    }
    let ret = match ck.ctx[t].0 {
      Term::Var(x, ty) => {
        let mut ty2 = self.lift.apply(ck, ty);
        for &ty in self.tys.iter().rev() {
          ty2 = ck.mk_fun(ty, ty2)
        }
        let (x, i) = ck.ctx[x].0;
        let x = ck.alloc((x, i + self.lift.f.inc));
        let mut t2 = ck.alloc(Term::Var(x, ty2));
        for i in (depth..depth + self.tys.len() as u32).rev() {
          let bv = ck.alloc(Term::Bound(i));
          t2 = ck.alloc(Term::App(t2, bv))
        }
        t2
      }
      Term::Free(x, ty) => {
        let ty2 = self.lift.apply(ck, ty);
        ck.alloc(Term::Free(x, ty2))
      }
      // `Logic.incr_indexes` lifts the types of constants too (`Const (c, incrT T)`);
      // leaving them alone desynchronises a constant's type from its arguments'.
      Term::Const(c, ty) => {
        let ty2 = self.lift.apply(ck, ty);
        ck.alloc(Term::Const(c, ty2))
      }
      Term::Abs(x, ty, e) => {
        let ty2 = self.lift.apply(ck, ty);
        let e2 = self.apply(ck, e, depth + 1);
        ck.alloc(Term::Abs(x, ty2, e2))
      }
      Term::App(t, u) => {
        let t2 = self.apply(ck, t, depth);
        let u2 = self.apply(ck, u, depth);
        ck.alloc(Term::App(t2, u2))
      }
      _ => t,
    };
    self.map.insert((t, depth), ret);
    ret
  }
}

struct Varify {
  subst: Vec<(StringId, SortId, TypeId)>,
}
impl Varify {
  fn new(mut subst: Vec<(StringId, SortId, TypeId)>) -> Self {
    subst.sort_by_key(|x| (x.0, x.1));
    // let ty = Mapper::new(Mapper::new(InstTypeCore::new(subst));
    Self { subst }
  }
}

impl Map<TypeId> for Varify {
  fn easy(subst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> Option<TypeId> {
    Some(match ck.ctx[t].0 {
      Type::Var(..) => t,
      Type::Free(i, s) => match subst.f.subst.binary_search_by_key(&(i, s), |x| (x.0, x.1)) {
        Ok(j) => subst.f.subst[j].2,
        _ => t,
      },
      _ => return None,
    })
  }
  fn apply(subst: &mut Mapper<TypeId, Self>, ck: &mut Checker<'_>, t: TypeId) -> TypeId {
    let Type::Type(c, tys) = ck.ctx[t].0 else { unreachable!() };
    let tys = tys.iter().map(|&t| subst.apply(ck, t)).collect::<Vec<_>>();
    ck.alloc_copy(&Type::Type(c, &tys))
  }
}

struct Comparer<I, F> {
  f: F,
  map: HashSet<(I, I)>,
}
trait Compare<I: Eq>: Sized {
  fn easy(_: &mut Comparer<I, Self>, _: &mut Checker<'_>, _: I, _: I) -> bool {
    false
  }
  fn apply(_: &mut Comparer<I, Self>, _: &mut Checker<'_>, t1: I, t2: I) {
    assert!(t1 == t2)
  }
}

impl<I: Eq> Compare<I> for () {
  fn easy(_: &mut Comparer<I, Self>, _: &mut Checker<'_>, t1: I, t2: I) -> bool {
    assert!(t1 == t2);
    true
  }
  fn apply(_: &mut Comparer<I, Self>, _: &mut Checker<'_>, _: I, _: I) {}
}

impl<I: Idx, F: Compare<I>> Comparer<I, F> {
  fn new(f: F) -> Self {
    Self { f, map: HashSet::new() }
  }

  fn apply(&mut self, ck: &mut Checker<'_>, t1: I, t2: I) {
    if F::easy(self, ck, t1, t2) {
      return;
    }
    if self.map.contains(&(t1, t2)) {
      return;
    }
    F::apply(self, ck, t1, t2);
    self.map.insert((t1, t2));
  }
}

impl<F: Compare<TermId>> Comparer<TermId, F> {
  fn apply_hyp(&mut self, ck: &mut Checker<'_>, h1: HypId, h2: HypId) {
    self.apply(ck, ck.ctx[h1].0, ck.ctx[h2].0)
  }
}

struct CompareTypes<T>(Comparer<TypeId, T>);

impl<T: Compare<TypeId>> CompareTypes<T> {
  fn new(f: T) -> Self {
    Self(Comparer::new(f))
  }
}
impl<T: Compare<TypeId>> Compare<TermId> for CompareTypes<T> {
  fn easy(_: &mut Comparer<TermId, Self>, ck: &mut Checker<'_>, t1: TermId, t2: TermId) -> bool {
    t1 == t2 && matches!(ck.ctx[t1].0, Term::Bound(_))
  }
  fn apply(subst: &mut Comparer<TermId, Self>, ck: &mut Checker<'_>, t1: TermId, t2: TermId) {
    match (&ck.ctx[t1].0, &ck.ctx[t2].0) {
      (&Term::Const(c1, ty1), &Term::Const(c2, ty2)) if c1 == c2 => subst.f.0.apply(ck, ty1, ty2),
      (&Term::Free(x1, ty1), &Term::Free(x2, ty2)) if x1 == x2 => subst.f.0.apply(ck, ty1, ty2),
      (&Term::Var(x1, ty1), &Term::Var(x2, ty2)) if x1 == x2 => subst.f.0.apply(ck, ty1, ty2),
      (&Term::Abs(_x1, ty1, e1), &Term::Abs(_x2, ty2, e2)) => {
        subst.f.0.apply(ck, ty1, ty2);
        subst.apply(ck, e1, e2);
      }
      (&Term::App(t1, u1), &Term::App(t2, u2)) => {
        subst.apply(ck, t1, t2);
        subst.apply(ck, u1, u2);
      }
      _ => panic!("term mismatch ({})", CMP_SITE.with(|c| c.get())),
    }
  }
}

struct StripSorts;
impl Compare<TypeId> for StripSorts {
  fn apply(map: &mut Comparer<TypeId, Self>, ck: &mut Checker<'_>, t1: TypeId, t2: TypeId) {
    match (&ck.ctx[t1].0, &ck.ctx[t2].0) {
      (&Type::Type(c1, tys1), &Type::Type(c2, tys2)) if c1 == c2 => {
        tys1.iter().zip(tys2).for_each(|(&ty1, &ty2)| map.apply(ck, ty1, ty2))
      }
      (&Type::Free(x1, _), &Type::Free(x2, SortId::TOP)) if x1 == x2 => {}
      (&Type::Var(x1, _), &Type::Var(x2, SortId::TOP)) if x1 == x2 => {}
      _ => panic!("type mismatch"),
    }
  }
}

thread_local! {
  /// which comparison is running, so a failure says what was being checked
  static CMP_SITE: std::cell::Cell<&'static str> = const { std::cell::Cell::new("") };
}
fn cmp_site(s: &'static str) {
  CMP_SITE.with(|c| c.set(s))
}

/// `AConv`, but a difference that the unifier deliberately left behind as a flex-flex pair
/// is accepted: `Unify.unifiers` returns those *unsolved*, and ML never re-compares the
/// disagreement pair at all -- it trusts the unifier.  The obligation does not disappear:
/// the pairs travel with the theorem and have to be discharged by `FlexFlex` before it can
/// be stored.
struct AConvModTpairs {
  tpairs: Vec<(TermId, TermId)>,
  /// `rename_bvars` renames some of a rule's schematic variables to the goal's parameter
  /// names, and `del_clashing` makes that renaming injective; recomputing it exactly is
  /// possible but brittle, so the new subgoals are compared modulo a consistent bijection
  /// on `Var` base names (`None` disables this, for the disagreement pair)
  vars: Option<(HashMap<StringId, StringId>, HashMap<StringId, StringId>)>,
  /// the variable names of the goal side of the disagreement pair: `rename_bvs` filters
  /// those out of the renaming (`Symset.member unknowns y`), so a rename onto one of them
  /// would capture, which the bijection alone does not rule out
  goal_vars: HashSet<StringId>,
}
impl AConvModTpairs {
  fn new(tpairs: Vec<(TermId, TermId)>) -> Self {
    Self { tpairs, vars: None, goal_vars: Default::default() }
  }

  fn modulo_renaming(tpairs: Vec<(TermId, TermId)>, goal_vars: HashSet<StringId>) -> Self {
    Self { tpairs, vars: Some(Default::default()), goal_vars }
  }
}
impl Compare<TermId> for AConvModTpairs {
  fn easy(_: &mut Comparer<TermId, Self>, _: &mut Checker<'_>, t1: TermId, t2: TermId) -> bool {
    t1 == t2
  }
  fn apply(subst: &mut Comparer<TermId, Self>, ck: &mut Checker<'_>, t1: TermId, t2: TermId) {
    // a recorded pair excuses the difference wherever it sits, including above the point
    // where the two sides first diverge
    if (subst.f.tpairs.iter()).any(|&(a, b)| (a, b) == (t1, t2) || (a, b) == (t2, t1)) {
      return
    }
    if let (&Term::Var(x1, ty1), &Term::Var(x2, ty2)) = (&ck.ctx[t1].0, &ck.ctx[t2].0) {
      if let Some((fwd, bwd)) = &mut subst.f.vars {
        let ((n1, i1), (n2, i2)) = (ck.ctx[x1].0, ck.ctx[x2].0);
        let ok = ty1 == ty2
          && i1 == i2
          && *fwd.entry(n1).or_insert(n2) == n2
          && *bwd.entry(n2).or_insert(n1) == n1
          && (n1 == n2 || !subst.f.goal_vars.contains(&n2));
        assert!(ok, "term mismatch ({})", CMP_SITE.with(|c| c.get()));
        return
      }
    }
    match (&ck.ctx[t1].0, &ck.ctx[t2].0) {
      (&Term::Abs(_x1, ty1, e1), &Term::Abs(_x2, ty2, e2)) if ty1 == ty2 => {
        subst.apply(ck, e1, e2);
      }
      (&Term::App(f1, u1), &Term::App(f2, u2)) => {
        subst.apply(ck, f1, f2);
        subst.apply(ck, u1, u2);
      }
      _ => {
        if *DEBUG_BC {
          println!("  [cmp] {:?}\n  [cmp] vs {:?}", ck.pp(t1), ck.pp(t2));
        }
        panic!("term mismatch ({})", CMP_SITE.with(|c| c.get()))
      }
    }
  }
}

struct AConv;
impl Compare<TermId> for AConv {
  fn easy(_: &mut Comparer<TermId, Self>, _: &mut Checker<'_>, t1: TermId, t2: TermId) -> bool {
    t1 == t2
  }
  fn apply(subst: &mut Comparer<TermId, Self>, ck: &mut Checker<'_>, t1: TermId, t2: TermId) {
    match (&ck.ctx[t1].0, &ck.ctx[t2].0) {
      (&Term::Abs(_x1, ty1, e1), &Term::Abs(_x2, ty2, e2)) if ty1 == ty2 => {
        subst.apply(ck, e1, e2);
      }
      (&Term::App(t1, u1), &Term::App(t2, u2)) => {
        subst.apply(ck, t1, t2);
        subst.apply(ck, u1, u2);
      }
      _ => panic!("term mismatch ({})", CMP_SITE.with(|c| c.get())),
    }
  }
}
