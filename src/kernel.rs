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
    self, proof, AssumptionId, ClassId, HasBinParse, IdMapping, IndexNameId, MaxIdx, Proof,
    ProofId, SortId, StringId, Subst, Term, TermId, ThmTrace, TypeId,
  },
  Global,
};

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
  /// if Err(i), then the largest Bound var blocking the type is i
  ty: Result<TypeId, u32>,
}

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
          Err(0) => {
            let lctx = ck.mk_lctx(LCtxId::NIL, dom);
            Ok(ck.get_type_ctx(lctx, e))
          }
          Err(i) => Err(i - 1),
        };
        TermData { sorts, maxidx, ty }
      }
      Term::App(e1, e2) => {
        let TermData { sorts: s1, maxidx: m1, ty: ty1 } = ck.ctx[e1].1;
        let TermData { sorts: s2, maxidx: m2, ty: _ } = ck.ctx[e2].1;
        let ty = ty1.map(|ty| ck.ctx[ty].0.as_fun().1);
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
  eq: Option<StringId>,
  imp: Option<TermId>,
  ofclass_cache: Option<OfClassCache>,
  alloc: &'a bumpalo::Bump,
  g: &'a Global,
}

impl StringId {
  const FUN: Self = Self(0);
  const PROP: Self = Self(1);
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
      eq: None,
      imp: None,
    };
    ck.alloc::<StringId>("fun");
    ck.alloc::<StringId>("prop");
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
    if self.ctx[c].0 != "Pure.imp" {
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
      let s = self.alloc("Pure.imp");
      let imp = self.alloc(Term::Const(s, ty));
      *self.imp.insert(imp)
    })
  }

  fn mk_imp(&mut self, a: TermId, b: TermId) -> TermId {
    let f = self.mk_imp_term();
    let f = self.alloc(Term::App(f, a));
    self.alloc(Term::App(f, b))
  }

  fn try_dest_forall(&self, a: TermId) -> Option<(TypeId, TermId)> {
    let (f, e) = self.try_dest_app(a)?;
    let (c, ty) = self.try_dest_const(f)?;
    if self.ctx[c].0 != "Pure.all" {
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

  fn mk_eq_str(&mut self) -> StringId {
    self.eq.unwrap_or_else(|| {
      let eq = self.alloc("Pure.eq");
      *self.eq.insert(eq)
    })
  }

  fn mk_eq(&mut self, a: TermId, b: TermId) -> TermId {
    let ty = self.ctx[a].1.ty.unwrap();
    let eq = self.mk_eq_str();
    let ty2 = self.mk_fun(ty, TypeId::PROP);
    let ty2 = self.mk_fun(ty, ty2);
    let eq = self.alloc(Term::Const(eq, ty2));
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

  fn check_hyp(&mut self, t: TermId) {
    let data = &self.ctx[t].1;
    assert!(data.maxidx.0 == 0 && self.ctx[data.ty.unwrap()].0.as_type().0 == StringId::PROP);
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
    println!("{}", pretty(&tr));
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
        (proof::Sorry | proof::Pruned, _) => panic!("encountered Sorry / Pruned"),
        (proof::Hyp, &[concl]) => {
          let concl: TermId = self.parse(&mut m, bp, concl);
          let shyps = self.ctx[concl].1.sorts;
          let hyp = self.alloc(concl);
          CProof { shyps, hyps: self.alloc(IdxBitSet::single(hyp)), concl }
        }
        (proof::ImpIntr, &[t, p]) => {
          let CProof { mut shyps, hyps, mut concl } = self.ctx[m.proofs[&p]].0;
          let t: TermId = self.parse(&mut m, bp, t);
          let mut hyps = self.ctx[hyps].0.clone();
          let TermData { sorts, ty, .. } = self.ctx[t].1;
          assert_eq!(ty, Ok(TypeId::PROP));
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
        (proof::ForallIntr, &[_, _]) => todo!(),
        (proof::ForallElim, &[t, p]) => {
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          let t: TermId = self.parse(&mut m, bp, t);
          let (ty2, pred) = self.dest_forall(concl);
          let TermData { sorts, ty, .. } = self.ctx[t].1;
          assert_eq!(ty, Ok(ty2));
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
        (proof::Refl, &[t]) => {
          let t = self.parse(&mut m, bp, t);
          let concl = self.mk_eq(t, t);
          CProof { shyps: self.ctx[concl].1.sorts, hyps: HypsId::EMPTY, concl }
        }
        (proof::Symm, &[_]) => todo!(),
        (proof::Trans, &[_, _]) => todo!(),
        (proof::BetaNorm, &[_]) => todo!(),
        (proof::BetaHead, &[_]) => todo!(),
        (proof::Eta, &[_]) => todo!(),
        (proof::EtaLong, &[_]) => todo!(),
        (proof::StripSHyps, &[sorts, p]) => {
          let CProof { mut shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
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
        (proof::AbsRule, &[_, _]) => todo!(),
        (proof::AppRule, &[_, _]) => todo!(),
        (proof::EqIntr, &[_, _]) => todo!(),
        (proof::EqElim, &[_, _]) => todo!(),
        (proof::FlexFlex, &[_, _]) => todo!(),
        (proof::Generalize, &[tfrees, frees, idx, p]) => {
          let mut inst = Mapper::new(GenTerm::new(
            self.parse(&mut m, bp, tfrees),
            self.parse(&mut m, bp, frees),
            self.parse(&mut m, bp, idx),
          ));
          let CProof { shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          CProof { shyps, hyps, concl: inst.apply(self, concl) }
        }
        (proof::Instantiate, &[tysubst, subst, p]) => {
          let mut inst = Mapper::new(InstTerm::new(
            self.parse(&mut m, bp, tysubst),
            self.parse(&mut m, bp, subst),
            false,
          ));
          let CProof { mut shyps, hyps, concl } = self.ctx[m.proofs[&p]].0;
          for &(_, _, ty) in &inst.f.ty.f.subst {
            shyps = self.union(shyps, self.ctx[ty].1.sorts);
          }
          for &(_, _, tm) in &inst.f.subst {
            shyps = self.union(shyps, self.ctx[tm].1.sorts);
          }
          CProof { shyps, hyps, concl: inst.apply(self, concl) }
        }
        (proof::Trivial, &[]) => todo!(),
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
          let mut bits = IdxBitSet::new();
          for s in bp.parse_list(shyps) {
            bits.insert(self.parse(&mut m, bp, s));
          }
          let shyps = self.alloc(bits);
          let mut bits = IdxBitSet::new();
          for h in bp.parse_list(hyps) {
            let h = self.parse(&mut m, bp, h);
            bits.insert(self.alloc(h));
          }
          let hyps = self.alloc(bits);
          CProof { shyps, hyps, concl: self.parse(&mut m, bp, prop) }
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
        (proof::Lift, &[gprop, inc, p]) => {
          let gprop: TermId = self.parse(&mut m, bp, gprop);
          let inc = self.parse(&mut m, bp, inc);
          let CProof { mut shyps, hyps, mut concl } = self.ctx[m.proofs[&p]].0;
          shyps = self.union(shyps, self.ctx[gprop].1.sorts);
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
        (proof::IncrIndexes, &[_, _]) => todo!(),
        (proof::Assumption, &[_, _]) => todo!(),
        (proof::EqAssumption, &[_]) => todo!(),
        (proof::Rotate, &[_, _, _]) => todo!(),
        (proof::PermutePrems, &[_, _, _]) => todo!(),
        (proof::Bicompose, &[env, tpairs, nsubgoal, flatten, as_, a_, n, nlift, p, q]) => {
          let CProof { shyps: shyps1, hyps: hyps1, concl } = self.ctx[m.proofs[&p]].0;
          let CProof { shyps: shyps2, hyps: hyps2, concl: lhs2 } = self.ctx[m.proofs[&q]].0;
          let (tysubst, subst) = self.parse(&mut m, bp, env);
          let mut inst = Mapper::new(InstTerm::new(tysubst, subst, true));
          let mut shyps = self.union(shyps1, shyps2);
          for (_, _, ty) in inst.f.ty.f.subst {
            shyps = self.union(shyps, self.ctx[ty].1.sorts)
          }
          let hyps = self.union(hyps1, hyps2);
          let (lhs, concl) = self.dest_imp(concl);
          Comparer::new(AConv).apply(self, lhs, lhs2);
          CProof { shyps, hyps, concl }
        }
        _ => panic!(),
      };
      // println!(
      //   "{pf:?} => {:?}, {:?} |- {:?}",
      //   self.pp(pf2.shyps),
      //   self.pp(pf2.hyps),
      //   self.pp(pf2.concl)
      // );
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
          let s = &self.ctx[s].0;
          assert!(classes.iter().any(|c| s.is_subset(c)))
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
  subst: Vec<(IndexNameId, SortId, TypeId)>,
}
impl InstType {
  fn new(mut subst: Vec<(IndexNameId, SortId, TypeId)>) -> Self {
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
  subst: Vec<(IndexNameId, TypeId, TermId)>,
  beta: bool,
}
impl InstTerm {
  fn new(
    tysubst: Vec<(IndexNameId, SortId, TypeId)>, mut subst: Vec<(IndexNameId, TypeId, TermId)>,
    beta: bool,
  ) -> Self {
    let ty = Mapper::new(InstType::new(tysubst));
    subst.sort_by_key(|x| (x.0, x.1));
    Self { ty, subst, beta }
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
        match inst.f.subst.binary_search_by_key(&(x, ty2), |x| (x.0, x.1)) {
          Ok(j) => inst.f.subst[j].2,
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
          let x = ck.alloc((x, inst.f.ty.f.idx));
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
      Term::Abs(x, ty, e) => {
        let e2 = self.apply(ck, e, depth + 1);
        ck.alloc(Term::Abs(x, ty, e2))
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
