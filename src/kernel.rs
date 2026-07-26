use std::{
  borrow::Borrow,
  collections::{BTreeSet, HashMap, HashSet},
  hash::Hash,
};

use dbg_pls::{pretty, DebugPls};
use ref_cast::RefCast;

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
static DEBUG_BC: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var_os("DEBUG_BC").is_some());

mk_id! {
  HypId(u32),
  HypsId(u32),
  SortsId(u32),
  LCtxId(u32),
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
      Type::Type(_, ts) => match ts {
        [] => TypeData { sorts: SortsId::EMPTY, maxidx: MaxIdx::NONE },
        &[t] => ck.ctx[t].1.clone(),
        _ => {
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
      Term::Const(_, ty) => {
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
            let rng = ck.get_type_ctx(lctx, e);
            Ok(ck.mk_fun(dom, rng))
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
      ofclass_cache: None,
      imp: None,
    };
    ck.alloc::<StringId>("fun");
    ck.alloc::<StringId>("prop");
    ck.alloc::<StringId>("Pure.eq");
    ck.alloc::<StringId>("Pure.imp");
    ck.alloc::<StringId>("Pure.all");
    ck.alloc::<HypsId>(IdxBitSet::new());
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
    let tdata = &self.ctx[t];
    if let Ok(ty) = tdata.1.ty {
      return ty;
    }
    if let Some(&ty) = self.type_cache.get(&(lctx, t)) {
      return ty;
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
        let ty = self.get_type_ctx(lctx2, e);
        self.mk_fun(dom, ty)
      }
      Term::App(e1, _) => {
        let ty = self.get_type_ctx(lctx, e1);
        self.ctx[ty].0.as_fun().1
      }
    };
    self.type_cache.insert((lctx, t), ty);
    ty
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

  pub fn check(&mut self, bp: &BinParser<'_>, tr: TagPtr) {
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
      let pf2 = match bp.get_enum(pf) {
        // debug wrapper (option prooftrace_props): the statement its subproof proves, so a
        // divergence is reported at the inference that caused it rather than at the end
        (proof::ZProp, &[prop, shyps, tpairs, p]) => {
          let cp = self.ctx[m.proofs[&p]].0.clone();
          let inner = bp.get_enum(p).0;

          let recorded: TermId = self.parse(&mut m, bp, prop);
          if !self.aconv(recorded, cp.concl, &mut HashSet::new()) {
            println!("!! statement mismatch after rule {inner}");
            println!("   computed: {:?}", self.pp(cp.concl));
            println!("   recorded: {:?}", self.pp(recorded));
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

          // we do not model flex-flex pairs yet: report rather than pass over them
          let n_tpairs = bp.parse_list(tpairs).count();
          if n_tpairs != 0 {
            println!("!! rule {inner} leaves {n_tpairs} flex-flex pair(s), which CProof does not carry");
          }
          cp
        }
        (proof::Sorry, _) => panic!("encountered Sorry (unrecorded proof: promise/future?)"),
        (proof::Pruned, _) => panic!("encountered Pruned (prune_proofs?)"),
        (proof::Hyp, &[concl, sorts]) => {
          let concl: TermId = self.parse(&mut m, bp, concl);
          // Thm.assume: "assume: variables" unless maxidx = ~1
          assert!(self.ctx[concl].1.maxidx == MaxIdx::NONE, "assume: variables");
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let hyp = self.alloc(concl);
          CProof { shyps, hyps: self.alloc(IdxBitSet::single(hyp)), concl }
        }
        (proof::ImpIntr, &[t, sorts, p]) => {
          let CProof { mut shyps, hyps, mut concl } = self.ctx[m.proofs[&p]].0;
          let t: TermId = self.parse(&mut m, bp, t);
          let mut hyps = self.ctx[hyps].0.clone();
          let TermData { ty, .. } = self.ctx[t].1;
          assert_eq!(ty, Ok(TypeId::PROP));
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          shyps = self.union(shyps, sorts);
          hyps.remove(self.alloc(t));
          concl = self.mk_imp(t, concl);
          CProof { shyps, hyps: self.alloc(hyps), concl }
        }
        (proof::ImpElim, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, concl } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: lhs2 } = self.ctx[m.proofs[&q]].0;
          let shyps = self.union(shyps1, shyps2);
          let hyps = self.union(hyps1, hyps2);
          let (lhs, concl) = self.dest_imp(concl);
          Comparer::new(AConv).apply(self, lhs, lhs2);
          CProof { shyps, hyps, concl }
        }
        // Thm.forall_intr: from `A` infer `⋀x. A`, x not free in the hypotheses.
        // shyps gains the sorts of x's type (`Sorts.union sorts shyps`).
        (proof::ForallIntr, &[x, sorts, p]) => {
          let x: TermId = self.parse(&mut m, bp, x);
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          if hyps != HypsId::EMPTY {
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
          CProof { shyps, hyps, concl: self.mk_forall(name, ty, body) }
        }
        (proof::ForallElim, &[t, sorts, p]) => {
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
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
          CProof { shyps, hyps, concl }
        }
        (proof::Axiom, &[name, concl, src]) => {
          let name: StringId = self.parse(&mut m, bp, name);
          let concl: TermId = self.parse(&mut m, bp, concl);
          let shyps = self.ctx[concl].1.sorts;
          println!("axiom {} / {src:?}: {:?}", self.pp(name), self.pp(concl));
          CProof { shyps, hyps: HypsId::EMPTY, concl }
        }
        (proof::Oracle, &[_, _]) => todo!(),
        (proof::Refl, &[t, sorts]) => {
          let t = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let concl = self.mk_eq(t, t);
          CProof { shyps, hyps: HypsId::EMPTY, concl }
        }
        // Thm.symmetric / Thm.transitive
        (proof::Symm, &[p]) => {
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          let (t, u) = self.dest_eq(concl);
          CProof { shyps, hyps, concl: self.mk_eq(u, t) }
        }
        (proof::Trans, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (t1, u1) = self.dest_eq(c1);
          let (u2, t2) = self.dest_eq(c2);
          Comparer::new(AConv).apply(self, u1, u2);
          let concl = self.mk_eq(t1, t2);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2), concl }
        }
        // Thm.beta_conversion true: `t ≡ Envir.beta_norm t`
        (proof::BetaNorm, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let rhs = BetaNorm::new().apply(self, t);
          let concl = self.mk_eq(t, rhs);
          CProof { shyps, hyps: HypsId::EMPTY, concl }
        }
        // Thm.beta_conversion false: one step at the head, `(λx. b) u ≡ b[u]`
        (proof::BetaHead, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let (f, u) = self.dest_app(t);
          let Term::Abs(_, _, b) = self.ctx[f].0 else { panic!("beta_conversion: not a redex") };
          let rhs = SubstBound::new(&[u]).apply(self, b, 0);
          let concl = self.mk_eq(t, rhs);
          CProof { shyps, hyps: HypsId::EMPTY, concl }
        }
        // Thm.eta_conversion: `t ≡ Envir.eta_contract t`
        (proof::Eta, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let rhs = EtaContract::new().apply(self, t);
          let concl = self.mk_eq(t, rhs);
          CProof { shyps, hyps: HypsId::EMPTY, concl }
        }
        (proof::EtaLong, &[_, _sorts]) => todo!(),
        (proof::StripSHyps, &[sorts, p]) => {
          let CProof { mut shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
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
          CProof { shyps, hyps, concl }
        }
        // Thm.abstract_rule: from `t ≡ u` infer `(λx. t) ≡ (λx. u)`, provided `x` is not
        // free in the hypotheses (the eigenvariable condition).
        (proof::AbsRule, &[x, p]) => {
          let x: TermId = self.parse(&mut m, bp, x);
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          let (t, u) = self.dest_eq(concl);
          if hyps != HypsId::EMPTY {
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
          CProof { shyps, hyps, concl: self.mk_eq(f, g) }
        }
        // Thm.combination: from `f ≡ g` and `t ≡ u` infer `f t ≡ g u`
        (proof::AppRule, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (f, g) = self.dest_eq(c1);
          let (t, u) = self.dest_eq(c2);
          let ft = self.alloc(Term::App(f, t));
          let gu = self.alloc(Term::App(g, u));
          let concl = self.mk_eq(ft, gu);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2), concl }
        }
        // Thm.equal_intr: from `A ⟹ B` and `B ⟹ A` infer `A ≡ B`
        (proof::EqIntr, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (a1, b1) = self.dest_imp(c1);
          let (b2, a2) = self.dest_imp(c2);
          let mut cmp = Comparer::new(AConv);
          cmp.apply(self, a1, a2);
          cmp.apply(self, b1, b2);
          let concl = self.mk_eq(a1, b1);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2), concl }
        }
        // Thm.equal_elim: from `A ≡ B` and `A` infer `B`
        (proof::EqElim, &[p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, concl: c1 } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: c2 } = self.ctx[m.proofs[&q]].0;
          let (a, b) = self.dest_eq(c1);
          Comparer::new(AConv).apply(self, a, c2);
          CProof { shyps: self.union(shyps1, shyps2), hyps: self.union(hyps1, hyps2), concl: b }
        }
        (proof::FlexFlex, &[_, _]) => todo!(),
        (proof::Generalize, &[tfrees, frees, idx, p]) => {
          // `Names.set` is `int Table.table` (a 2-3 tree), not a list: exportSmall dumps the
          // table itself, where the old XML encoder flattened it via `Names.dest`.
          let tfrees: Table<StringId, u32> = self.parse(&mut m, bp, tfrees);
          let frees: Table<StringId, u32> = self.parse(&mut m, bp, frees);
          let idx = self.parse(&mut m, bp, idx);
          let mut inst = Mapper::new(GenTerm::new(
            tfrees.0.into_iter().map(|(x, _)| x).collect(),
            frees.0.into_iter().map(|(x, _)| x).collect(),
            idx,
          ));
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          CProof { shyps, hyps, concl: inst.apply(self, concl) }
        }
        (proof::Instantiate, &[tysubst, subst, sorts, p]) => {
          let mut inst = Mapper::new(InstTerm::new(
            Subst::from_assoc(&mut (&mut *self, &mut m), bp, tysubst, subst),
            false,
            false,
          ));
          let CProof { hyps, concl, .. } = self.ctx[m.proofs[&p]].0;
          // Thm.instantiate sets shyps = shyps' outright, and prep_insts derives that from
          // the *certified* Ctyp/Cterm sorts, which are inherited and so cannot be
          // recomputed from the raw types and terms recorded here.
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          for &(v, vs, ty) in &inst.f.ty.f.subst.clone() {
            if *DEBUG_BC {
              println!("  [inst] tyvar {:?}:{:?} := {:?} contributing {:?}", self.pp(v),
                self.pp(vs), self.pp(ty), self.pp(self.ctx[ty].1.sorts));
            }
          }
          for &(v, vt, tm) in &inst.f.subst.clone() {
            if *DEBUG_BC {
              println!("  [inst] var {:?}:{:?} := {:?} contributing {:?}", self.pp(v),
                self.pp(vt), self.pp(tm), self.pp(self.ctx[tm].1.sorts));
            }
          }
          CProof { shyps, hyps, concl: inst.apply(self, concl) }
        }
        // Thm.trivial: from a proposition A, the theorem A ==> A
        (proof::Trivial, &[t, sorts]) => {
          let t: TermId = self.parse(&mut m, bp, t);
          let shyps = self.parse_sorts(&mut m, bp, sorts);
          let concl = self.mk_imp(t, t);
          CProof { shyps, hyps: HypsId::EMPTY, concl }
        }
        (proof::OfClass, &[ty, c]) => {
          let OfClassCache { itself, type_ } = self.ofclass_cache.unwrap_or_else(|| {
            let itself = self.alloc("itself");
            let type_ = self.alloc("Pure.type");
            *self.ofclass_cache.insert(OfClassCache { itself, type_ })
          });
          let c = self.alloc_copy(&&*format!(
            "{}_class",
            std::str::from_utf8(bp.get(c.as_ptr()).as_str()).unwrap()
          ));
          let ty = self.parse(&mut m, bp, ty);
          let itself_t = self.alloc_copy(&Type::Type(itself, &[ty]));
          let cty = self.mk_fun(itself_t, TypeId::PROP);
          let c = self.alloc(Term::Const(c, cty));
          let ty2 = self.alloc(Term::Const(type_, itself_t));
          let concl: TermId = self.alloc(Term::App(c, ty2));
          CProof { shyps: self.ctx[concl].1.sorts, hyps: HypsId::EMPTY, concl }
        }
        (proof::Thm, &[_i]) => todo!(),
        (proof::ConstrainThm, &[_i, shyps, hyps, prop]) => {
          // the referenced theorem's own sort hypotheses, which the using theorem inherits
          let shyps = self.parse_sorts(&mut m, bp, shyps);
          let mut hyp_terms = vec![];
          let mut bits = IdxBitSet::new();
          for h in bp.parse_list(hyps) {
            let h = self.parse(&mut m, bp, h);
            hyp_terms.push(h);
            bits.insert(self.alloc(h));
          }
          let hyps = self.alloc(bits);
          // `prepare_thm_proof` records `prop = Logic.list_implies (hyps, concl)`, and the
          // reference is used applied to those hypotheses (`argsP = … map Hyp hyps`).  So
          // strip them back off, keeping them as hypotheses -- leaving them as premises as
          // well would count each one twice.
          let mut concl: TermId = self.parse(&mut m, bp, prop);
          let mut cmp = Comparer::new(AConv);
          for &h in &hyp_terms {
            let (arg, rest) = self.dest_imp(concl);
            cmp.apply(self, h, arg);
            concl = rest
          }
          CProof { shyps, hyps, concl }
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
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          CProof { shyps, hyps, concl: inst.apply(self, concl) }
        }
        (proof::LegacyFreezeT, &[_]) => todo!(),
        (proof::Lift, &[gprop, inc, sorts, p]) => {
          let gprop: TermId = self.parse(&mut m, bp, gprop);
          let inc = self.parse(&mut m, bp, inc);
          let sorts = self.parse_sorts(&mut m, bp, sorts);
          let CProof { mut shyps, hyps, mut concl } = self.ctx[m.proofs[&p]].0;
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
          CProof { shyps, hyps, concl }
        }
        // Thm.incr_indexes: raise every schematic index by `inc`; hyps and shyps are untouched
        (proof::IncrIndexes, &[inc, p]) => {
          let inc: u32 = self.parse(&mut m, bp, inc);
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          let concl =
            if inc == 0 { concl } else { Mapper::new(IncrIdx::new(inc)).apply(self, concl) };
          CProof { shyps, hyps, concl }
        }
        (proof::Assumption, &[_, _]) => todo!(),
        (proof::EqAssumption, &[_]) => todo!(),
        (proof::Rotate, &[_, _, _]) => todo!(),
        (proof::PermutePrems, &[_, _, _]) => todo!(),
        // Thm.bicompose_aux: the rule `⟦rAs⟧ ⟹ B` is resolved against subgoal `Bi` of the
        // state `⟦Bs; Bi⟧ ⟹ C`, giving `⟦Bs; As⟧ ⟹ C` under the unifier `env`.
        // `p` proves the rule, `q` proves the state (thm.ML: deriv_rule2 … rder' sder).
        (proof::Bicompose, &[args, p, q]) => {
          let args: BicomposeArgs = self.parse(&mut m, bp, args);
          let CProof { shyps: shyps1, hyps: hyps1, concl: rule } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: state } = self.ctx[m.proofs[&q]].0;
          if args.n != 0 {
            todo!("eresolution: discharge the rule's first premise against assumption {}", args.n)
          }
          assert!(args.tpairs.is_empty(), "flex-flex pairs are not carried by CProof");

          // rule = ⟦rAs⟧ ⟹ B
          let mut r_prems = vec![];
          let mut b = rule;
          for _ in 0..args.nsubgoal {
            let (h, t) = self.dest_imp(b);
            r_prems.push(h);
            b = t
          }
          // state = ⟦Bs; Bi⟧ ⟹ C
          let mut bs = vec![];
          let mut st = state;
          for _ in 0..args.nbs {
            let (h, t) = self.dest_imp(st);
            bs.push(h);
            st = t
          }
          let (bi, c) = self.dest_imp(st);

          if *DEBUG_BC {
            println!("  [bc] nbs={} nsubgoal={} flatten={} n={} nlift={} tpairs={} as={}",
              args.nbs, args.nsubgoal, args.flatten, args.n, args.nlift,
              args.tpairs.len(), args.as_.len());
            println!("       p(rule?)  = {:?}", self.pp(rule));
            println!("       q(state?) = {:?}", self.pp(state));
          }
          let mut inst = Mapper::new(InstTerm::new(args.env, true, true));
          // the unifier is what justifies replacing the subgoal by the rule's premises
          let b = inst.apply(self, b);
          let bi = inst.apply(self, bi);
          Comparer::new(AConv).apply(self, b, bi);

          let mut concl = inst.apply(self, c);
          for &a in r_prems.iter().rev() {
            let a = if args.flatten { self.flatten_params(args.n, a) } else { a };
            let a = inst.apply(self, a);
            concl = self.mk_imp(a, concl)
          }
          for &bj in bs.iter().rev() {
            let bj = inst.apply(self, bj);
            concl = self.mk_imp(bj, concl)
          }

          // `Envir.insert_sorts` folds over the *type* env only
          // (`Vartab.fold (Sorts.insert_typ o #2 o #2) o type_env`): the terms assigned by
          // the term env are already accounted for in the premises' own shyps.
          let mut shyps = self.union(shyps1, shyps2);
          for &(_, _, ty) in &inst.f.ty.f.subst {
            shyps = self.union(shyps, self.ctx[ty].1.sorts)
          }
          CProof { shyps, hyps: self.union(hyps1, hyps2), concl }
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
      m.proofs.insert(pf, self.alloc(pf2));
    }
    let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&tr.root]].0;
    // println!(
    //   "want: {:?},\ngot: {:?}, {:?} |- {:?}",
    //   self.pp(prop),
    //   self.pp(shyps),
    //   self.pp(hyps),
    //   self.pp(concl)
    // );
    let mut compare = Comparer::new(CompareTypes::new(StripSorts));
    let mut inst_var = Mapper::new(MapTypes::new(InstTVars::new(tr.unconstrain_var_map)));
    if tr.unconstrain_shyps != 0 || shyps != SortsId::EMPTY {
      let mut classes = HashMap::<IndexNameId, IdxBitSet<ClassId>>::new();
      for _ in 0..tr.unconstrain_shyps {
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
            println!("   unconstrain_shyps = {}", tr.unconstrain_shyps);
            println!("   classes = {:?}",
              classes.iter().map(|c| c.iter().map(|c| self.pp(c)).collect::<Vec<_>>())
                .collect::<Vec<_>>());
            println!("   all shyps = {:?}", self.pp(shyps));
          }
          assert!(classes.iter().any(|c| sc.is_subset(c)))
        }
      }
    }
    if hyps != HypsId::EMPTY || !tr.unconstrain_hyps.is_empty() {
      let mut hyps = self.ctx[hyps].0.clone();
      for &h in &tr.unconstrain_hyps {
        hyps.remove(self.alloc(h));
        let (arg, rest) = self.dest_imp(prop);
        let h = inst_var.apply(self, h);
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
      ck.alloc(t2)
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
}
impl InstType {
  fn new(mut subst: Box<[(IndexNameId, SortId, TypeId)]>) -> Self {
    subst.sort_by_key(|x| (x.0, x.1));
    Self { subst }
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
        Ok(j) => inst.f.subst[j].2,
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

struct InstTerm {
  ty: Mapper<TypeId, InstType>,
  subst: Box<[(IndexNameId, TypeId, TermId)]>,
  beta: bool,
  /// An `Envir` keys its `tenv` by the variable's type *before* type instantiation
  /// (`Envir.norm_term1` looks the variable up as it stands in the term), whereas a
  /// `Thm.instantiate` substitution is keyed by the instantiated type.
  env_keys: bool,
}
impl InstTerm {
  fn new(mut subst: Subst, beta: bool, env_keys: bool) -> Self {
    let ty = Mapper::new(InstType::new(subst.tysubst));
    subst.subst.sort_by_key(|x| (x.0, x.1));
    Self { ty, subst: subst.subst, beta, env_keys }
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
        let key = if inst.f.env_keys { ty } else { ty2 };
        match inst.f.subst.binary_search_by_key(&(x, key), |x| (x.0, x.1)) {
          // `Envir.norm_term` normalises the result again: a unifier need not be idempotent
          Ok(j) => {
            let t = inst.f.subst[j].2;
            inst.apply(ck, t)
          }
          _ => ck.alloc(Term::Var(x, ty2)),
        }
      }
      Term::Abs(x, ty, e) => {
        let ty2 = inst.f.ty.apply(ck, ty);
        let e2 = inst.apply(ck, e);
        ck.alloc(Term::Abs(x, ty2, e2))
      }
      Term::App(t, u) => {
        if inst.f.beta {
          if let Term::Abs(_, _, b) = ck.ctx[t].0 {
            let t2 = SubstBound::new(&[u]).apply(ck, b, 0);
            return inst.apply(ck, t2);
          }
        }
        let t2 = inst.apply(ck, t);
        if inst.f.beta {
          if let Term::Abs(_, _, b) = ck.ctx[t2].0 {
            let t2 = SubstBound::new(&[u]).apply(ck, b, 0);
            return inst.apply(ck, t2);
          }
        }
        let u2 = inst.apply(ck, u);
        ck.alloc(Term::App(t2, u2))
      }
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
      _ => panic!("term mismatch"),
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
      _ => panic!("term mismatch"),
    }
  }
}
