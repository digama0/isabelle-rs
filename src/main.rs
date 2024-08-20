use ast::Entry;
use itertools::Itertools;
use kernel::Checker;
use lalrpop_util::lalrpop_mod;
use rusqlite::{Connection, Result};
use std::collections::{HashMap, HashSet};
use std::io::Read;
use std::path::Path;
use trace::ThmTrace;

pub mod ast;
pub mod idx;
pub mod kernel;
pub mod trace;

enum Tree<'a> {
  Text(&'a [u8]),
  Elem(&'a [u8], Attrs<'a>, Trees<'a>),
  Properties(Attrs<'a>),
  Node(Trees<'a>),
}

impl<'a> std::fmt::Debug for Tree<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Text(s) => write!(f, "{:?}", std::str::from_utf8(s).unwrap()),
      Self::Elem(name, attrs, ts) => {
        write!(f, "{}", std::str::from_utf8(name).unwrap())?;
        if !attrs.is_empty() {
          write!(f, "{attrs:?}")?;
        }
        let mut iter = f.debug_tuple("");
        ts.iter().for_each(|i| {
          iter.field(i);
        });
        iter.finish()
      }
      Self::Properties(props) => write!(f, "props{props:?}"),
      Self::Node(ts) => {
        let mut iter = f.debug_list();
        ts.iter().for_each(|i| {
          iter.entry(i);
        });
        iter.finish()
      }
    }
  }
}
type Trees<'a> = Box<[Tree<'a>]>;

// fn of_str(chunk: &[u8]) -> String {
//   std::str::from_utf8(chunk).unwrap().to_owned()
// }

const X: u8 = 5;
const Y: u8 = 6;

#[derive(Clone)]
struct Separated<'a, const N: u8>(Option<&'a [u8]>);
type Attrs<'a> = Separated<'a, Y>;

impl<'a, const N: u8> Separated<'a, N> {
  fn new(buf: &'a [u8]) -> Self {
    Self(if buf.is_empty() { None } else { Some(buf) })
  }
  fn is_empty(&self) -> bool {
    self.0.is_none()
  }
}

impl<'a> Separated<'a, Y> {
  fn vector(self) -> VectorIter<'a> {
    VectorIter { count: 0, iter: self }
  }
  fn split(a: &[u8]) -> (&[u8], &[u8]) {
    let j = a.iter().position(|&i| i == b'=').unwrap();
    (&a[..j], &a[j + 1..])
  }
}

impl<'a, const N: u8> Iterator for Separated<'a, N> {
  type Item = &'a [u8];
  fn next(&mut self) -> Option<Self::Item> {
    let chunk = self.0?;
    let (now, later) = match chunk.iter().position(|&i| i == N) {
      Some(i) => (&chunk[..i], Some(&chunk[i + 1..])),
      None => (chunk, None),
    };
    self.0 = later;
    Some(now)
  }
}
impl<'a, const N: u8> std::fmt::Debug for Separated<'a, N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt(
      &self.clone().map(|x| std::str::from_utf8(x).unwrap()).collect::<Vec<_>>(),
      f,
    )
  }
}

struct VectorIter<'a> {
  count: usize,
  iter: Separated<'a, Y>,
}
impl<'a> VectorIter<'a> {
  fn is_empty(&self) -> bool {
    self.iter.is_empty()
  }

  fn take_n<const N: usize>(mut self) -> [String; N] {
    let out = [(); N].map(|_| std::str::from_utf8(self.next().unwrap()).unwrap().to_owned());
    assert!(self.is_empty());
    out
  }
  fn indexname(mut self) -> (String, usize) {
    let s = std::str::from_utf8(self.next().unwrap()).unwrap().to_owned();
    let t = self.next().map_or(0, |i| std::str::from_utf8(i).unwrap().parse().unwrap());
    assert!(self.is_empty());
    (s, t)
  }
}
impl<'a> Iterator for VectorIter<'a> {
  type Item = &'a [u8];

  fn next(&mut self) -> Option<Self::Item> {
    let a = self.iter.next()?;
    let i = self.count;
    self.count += 1;
    let (lhs, rhs) = Separated::split(a);
    assert!(std::str::from_utf8(lhs).unwrap().parse::<usize>().unwrap() == i);
    Some(rhs)
  }
}

fn parse(bytes: &[u8]) -> Trees<'_> {
  let mut stack = vec![];
  let mut markup = None::<(&[u8], Attrs<'_>)>;
  let mut head = vec![];
  for chunk in Separated::<X>::new(bytes) {
    if chunk.is_empty() {
      continue;
    }
    if let [Y, chunk @ ..] = chunk {
      if chunk.is_empty() {
        let (name, attrs) = markup.unwrap();
        let body = head;
        (markup, head) = stack.pop().unwrap();
        head.push(match name {
          b":" if body.is_empty() => Tree::Properties(attrs),
          b":" if attrs.is_empty() => Tree::Node(body.into()),
          _ => Tree::Elem(name, attrs, body.into()),
        })
      } else {
        let mut iter = Separated::<Y>::new(chunk);
        let name = iter.next().unwrap();
        stack.push((markup, head));
        (markup, head) = (Some((name, iter)), vec![])
      }
    } else {
      for chunk in Separated::<Y>::new(chunk) {
        head.push(Tree::Text(chunk))
      }
    }
  }
  assert!(stack.is_empty() && markup.is_none());
  head.into()
}

trait Parse<'a>: Sized {
  fn parse1(_: &Tree<'a>) -> Self {
    unimplemented!("parse1")
  }
  fn parse(this: &[Tree<'a>]) -> Self {
    let [a] = this else { panic!() };
    Self::parse1(a)
  }
  fn parse1_node(t: &Tree<'a>) -> Self {
    Self::parse(t.as_node())
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    Self::parse1(t)
  }
}
impl<'a> Parse<'a> for &'a str {
  fn parse1(t: &Tree<'a>) -> Self {
    let Tree::Text(a) = *t else { panic!() };
    std::str::from_utf8(a).unwrap()
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    match *t.as_node() {
      [Tree::Text(a)] => std::str::from_utf8(a).unwrap(),
      [] => "",
      _ => panic!(),
    }
  }
}
impl<'a> Parse<'a> for String {
  fn parse1(t: &Tree<'a>) -> Self {
    <&str>::parse1(t).to_owned()
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    <&str>::parse_v2(t).to_owned()
  }
}
impl<'a> Parse<'a> for usize {
  fn parse1(t: &Tree<'a>) -> Self {
    <&str>::parse1(t).parse().unwrap()
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    <&str>::parse_v2(t).parse().unwrap()
  }
}
impl<'a> Parse<'a> for u32 {
  fn parse1(t: &Tree<'a>) -> Self {
    <&str>::parse1(t).parse().unwrap()
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    <&str>::parse_v2(t).parse().unwrap()
  }
}
impl<'a> Parse<'a> for i32 {
  fn parse1(t: &Tree<'a>) -> Self {
    <&str>::parse1(t).parse().unwrap()
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    let s = <&str>::parse_v2(t);
    if let Some(s) = s.strip_prefix("~") {
      -s.parse::<i32>().unwrap()
    } else {
      s.parse().unwrap()
    }
  }
}
impl<'a> Parse<'a> for bool {
  fn parse1(t: &Tree<'a>) -> Self {
    match <&str>::parse1(t) {
      "0" => false,
      "1" => true,
      _ => panic!(),
    }
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    match <&str>::parse_v2(t) {
      "0" => false,
      "1" => true,
      _ => panic!(),
    }
  }
}
impl<'a> Parse<'a> for () {
  fn parse1(t: &Tree<'a>) -> Self {
    assert_eq!(<&str>::parse1(t), "")
  }
  fn parse(t: &[Tree<'a>]) -> Self {
    assert!(t.is_empty())
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    assert!(t.as_node().is_empty())
  }
}
impl<'a, A: Parse<'a>, B: Parse<'a>> Parse<'a> for (A, B) {
  fn parse(t: &[Tree<'a>]) -> Self {
    let [a, b] = t else { panic!() };
    (A::parse1_node(a), B::parse1_node(b))
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    let [a, b] = t.as_node() else { panic!() };
    (A::parse_v2(a), B::parse_v2(b))
  }
}
impl<'a, A: Parse<'a>, B: Parse<'a>, C: Parse<'a>> Parse<'a> for (A, B, C) {
  fn parse(t: &[Tree<'a>]) -> Self {
    let [a, b, c] = t else { panic!() };
    (A::parse1_node(a), B::parse1_node(b), C::parse1_node(c))
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    let [a, b, c] = t.as_node() else { panic!() };
    (A::parse_v2(a), B::parse_v2(b), C::parse_v2(c))
  }
}
impl<'a, A: Parse<'a>, B: Parse<'a>, C: Parse<'a>, D: Parse<'a>> Parse<'a> for (A, B, C, D) {
  fn parse(t: &[Tree<'a>]) -> Self {
    let [a, b, c, d] = t else { panic!() };
    (A::parse1_node(a), B::parse1_node(b), C::parse1_node(c), D::parse1_node(d))
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    let [a, b, c, d] = t.as_node() else { panic!() };
    (A::parse_v2(a), B::parse_v2(b), C::parse_v2(c), D::parse_v2(d))
  }
}
impl<'a, T: Parse<'a>> Parse<'a> for Vec<T> {
  fn parse(t: &[Tree<'a>]) -> Self {
    t.iter().map(|a| T::parse1_node(a)).collect()
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    t.as_node().iter().map(|a| T::parse_v2(a)).collect()
  }
}
impl<'a, T: Parse<'a>> Parse<'a> for Box<T> {
  fn parse(t: &[Tree<'a>]) -> Self {
    Box::new(T::parse(t))
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    Box::new(T::parse_v2(t))
  }
}
impl<'a, T: Parse<'a>> Parse<'a> for Box<[T]> {
  fn parse(t: &[Tree<'a>]) -> Self {
    t.iter().map(|a| T::parse1_node(a)).collect()
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    t.as_node().iter().map(|a| T::parse_v2(a)).collect()
  }
}
impl<'a, T: Parse<'a>> Parse<'a> for Option<T> {
  fn parse(t: &[Tree<'a>]) -> Self {
    match t {
      [] => None,
      [a] => Some(T::parse(a.as_node())),
      _ => panic!(),
    }
  }
  fn parse_v2(t: &Tree<'a>) -> Self {
    match t.as_node() {
      [] => None,
      [a] => Some(T::parse_v2(a)),
      _ => panic!(),
    }
  }
}

// macro_rules! impl_parse_for_enum {
//   (impl Parse<$a:lifetime> for $ty:ty { $($body:tt)* }) => {
//     impl<$a> Parse<$a> for $ty {
//       fn parse1(t: &Tree<$a>) -> Self {
//         let (tag, mut attrs, ts) = t.as_tagged();
//         match tag {

//         }
//         let fns: &[] = &[$(|$ts: &[Tree<'_>]| impl_parse_for_enum! (@impl $arm = attrs => $e)),*];
//         fns[tag](ts)
//       }
//     }
//   };
//   (@go ($i:expr) $($arm:tt, $ts:ident => $e:expr,)*) => {

//   }
//   (@arm [$($x:ident),*] = $attrs:ident => $e:expr) => {{
//     $(let $x = $attrs.next();)*
//     assert!($attrs.is_empty());
//     $e
//   }};
// }

type Class = String;
type Sort = Vec<Class>;

fn short_name(s: &str) -> &str {
  match s.split_once('.') {
    Some((_, s)) => s,
    _ => s,
  }
}

enum Type {
  #[allow(clippy::enum_variant_names)]
  Type(String, Vec<Type>),
  Free(String, Sort),
  Var(String, u32, Sort),
}

impl std::fmt::Debug for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Type(t, ts) => {
        if "fun" == t {
          write!(f, "({:?} -> {:?})", ts[0], ts[1])?;
        } else {
          write!(f, "{}", short_name(t))?;
          if !ts.is_empty() {
            write!(f, "[{:?}]", ts.iter().format(", "))?;
          }
        }
        Ok(())
      }
      Self::Free(t, ts) => {
        write!(f, "{t}")?;
        if !ts.is_empty() {
          write!(f, "<:{}", ts.iter().format("+"))?;
        }
        Ok(())
      }
      Self::Var(c, i, ts) => {
        write!(f, "{c}.{i}")?;
        if !ts.is_empty() {
          write!(f, "[{:?}]", ts.iter().format(", "))?;
        }
        Ok(())
      }
    }
  }
}

impl<'a> Parse<'a> for Type {
  fn parse1(t: &Tree<'a>) -> Self {
    let (tag, attrs, ts) = t.as_tagged();
    match tag {
      0 => {
        let [x] = attrs.take_n();
        Type::Type(x, <_>::parse(ts))
      }
      1 => {
        let [x] = attrs.take_n();
        Type::Free(x, <_>::parse(ts))
      }
      // 2 => {
      //   let (x, i) = attrs.indexname();
      //   Type::Var(x, i, <_>::parse(ts))
      // }
      _ => panic!(),
    }
  }
}

enum Term {
  #[allow(clippy::enum_variant_names)]
  Const(String, Vec<Type>),
  Const2(String, Box<Type>),
  Free(String, Option<Box<Type>>),
  Var(String, u32, Option<Box<Type>>),
  Bound(u32),
  Abs(String, Box<Type>, Box<Term>),
  App(Box<Term>, Box<Term>),
  OfClass(String, Box<Term>),
}

impl Term {
  fn dbg_fmt<'a>(
    &'a self, ctx: &mut Vec<&'a String>, f: &mut std::fmt::Formatter<'_>,
  ) -> std::fmt::Result {
    match self {
      Term::Const(c, cs) => {
        write!(f, "{}", short_name(c))?;
        if !cs.is_empty() {
          write!(f, "({:?})", cs.iter().format(", "))?;
        }
        Ok(())
      }
      Term::Const2(c, ty) => write!(f, "{c}:{ty:?}"),
      Term::Free(v, None) => write!(f, "{v}"),
      Term::Free(v, Some(ty)) => write!(f, "{v}:{ty:?}"),
      Term::Var(v, i, None) => write!(f, "v.{v}.{i}"),
      Term::Var(v, i, Some(ty)) => write!(f, "v.{v}.{i}:{ty:?}"),
      &Term::Bound(i) => write!(f, "{}", ctx[ctx.len() - i as usize - 1]),
      Term::Abs(x, ty, e) => {
        write!(f, "(fun {x}: {ty:?} => ")?;
        ctx.push(x);
        e.dbg_fmt(ctx, f)?;
        ctx.pop();
        write!(f, ")")
      }
      Term::App(..) => {
        fn rec_app<'a>(
          t: &'a Term, ctx: &mut Vec<&'a String>, f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
          if let Term::App(g, a) = t {
            rec_app(g, ctx, f)?;
            write!(f, " ")?;
            a.dbg_fmt(ctx, f)
          } else {
            t.dbg_fmt(ctx, f)
          }
        }
        write!(f, "(")?;
        rec_app(self, ctx, f)?;
        write!(f, ")")
      }
      Term::OfClass(c, cs) => {
        write!(f, "OfClass({}, ", short_name(c))?;
        cs.dbg_fmt(ctx, f)?;
        write!(f, ")")
      }
    }
  }
}

impl std::fmt::Debug for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.dbg_fmt(&mut vec![], f)
  }
}

struct OptBox<T>(Option<Box<T>>);
impl<T: std::fmt::Debug> std::fmt::Debug for OptBox<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.0.fmt(f)
  }
}
impl<'a, T: Parse<'a>> Parse<'a> for OptBox<T> {
  fn parse(this: &[Tree<'a>]) -> Self {
    if this.is_empty() {
      Self(None)
    } else {
      Self(Some(<_>::parse(this)))
    }
  }
}

impl<'a> Parse<'a> for Term {
  fn parse1(t: &Tree<'a>) -> Self {
    let (tag, attrs, ts) = t.as_tagged();
    match tag {
      0 => {
        let [x] = attrs.take_n();
        Term::Const(x, <_>::parse(ts))
      }
      1 => {
        let [x] = attrs.take_n();
        Term::Free(x, OptBox::parse(ts).0)
      }
      // 2 => {
      //   let (x, i) = attrs.indexname();
      //   Term::Var(x, i, OptBox::parse(ts).0)
      // }
      3 => {
        let [] = attrs.take_n();
        Term::Bound(<_>::parse(ts))
      }
      4 => {
        let [x] = attrs.take_n();
        let (y, z) = <_>::parse(ts);
        Term::Abs(x, y, z)
      }
      5 => {
        let [] = attrs.take_n();
        let (f, a) = <_>::parse(ts);
        Term::App(f, a)
      }
      6 => {
        let [x] = attrs.take_n();
        Term::OfClass(x, <_>::parse(ts))
      }
      _ => panic!(),
    }
  }
}

enum Proof {
  Sorry,
  Bound(usize),
  AbsT(String, Box<Type>, Box<Proof>),
  AbsP(String, Box<Term>, Box<Proof>),
  AppT(Box<Proof>, Box<Term>),
  AppP(Box<Proof>, Box<Proof>),
  Hyp(Box<Term>),
  Axiom(String, Vec<Type>),
  OfClass(Box<Type>, String),
  Oracle(String, Box<Term>, Vec<Type>),
  Thm { serial: usize, theory_name: String, thm_name: (String, usize), tyargs: Vec<Type> },
}

impl Proof {
  fn dbg_fmt<'a>(
    &'a self, hctx: &mut Vec<&'a String>, ctx: &mut Vec<&'a String>,
    f: &mut std::fmt::Formatter<'_>,
  ) -> std::fmt::Result {
    match self {
      Self::Sorry => write!(f, "Sorry"),
      Self::Bound(i) => write!(f, "{}", hctx[hctx.len() - i - 1]),
      Self::AbsT(x, ty, e) => {
        write!(f, "(fun {x}: {ty:?} => ")?;
        ctx.push(x);
        e.dbg_fmt(hctx, ctx, f)?;
        ctx.pop();
        write!(f, ")")
      }
      Self::AbsP(x, tm, e) => {
        write!(f, "(assume {x}: ")?;
        tm.dbg_fmt(ctx, f)?;
        write!(f, " => ")?;
        hctx.push(x);
        e.dbg_fmt(hctx, ctx, f)?;
        hctx.pop();
        write!(f, ")")
      }
      Self::AppT(..) | Self::AppP(..) => {
        fn rec_app<'a>(
          p: &'a Proof, hctx: &mut Vec<&'a String>, ctx: &mut Vec<&'a String>,
          f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
          match p {
            Proof::AppT(g, a) => {
              rec_app(g, hctx, ctx, f)?;
              write!(f, " ")?;
              a.dbg_fmt(ctx, f)
            }
            Proof::AppP(g, a) => {
              rec_app(g, hctx, ctx, f)?;
              write!(f, " ")?;
              a.dbg_fmt(hctx, ctx, f)
            }
            _ => p.dbg_fmt(hctx, ctx, f),
          }
        }
        write!(f, "(")?;
        rec_app(self, hctx, ctx, f)?;
        write!(f, ")")
      }
      Self::Hyp(tm) => {
        write!(f, "(hyp ")?;
        tm.dbg_fmt(ctx, f)?;
        write!(f, ")")
      }
      Self::Axiom(s, ty) => {
        write!(f, "axiom[{s}]")?;
        if !ty.is_empty() {
          write!(f, "({:?})", ty.iter().format(", "))?;
        }
        Ok(())
      }
      Self::OfClass(ty, c) => write!(f, "ofClass({ty:?}, {c})"),
      Self::Oracle(s, tm, ty) => {
        write!(f, "oracle[{s}](")?;
        tm.dbg_fmt(ctx, f)?;
        write!(f, ", {ty:?})")
      }
      Self::Thm { serial, theory_name, thm_name, tyargs } => {
        write!(f, "thm[{theory_name}.{thm_name:?}/{serial}]")?;
        if !tyargs.is_empty() {
          write!(f, "({:?})", tyargs.iter().format(", "))?;
        }
        Ok(())
      }
    }
  }
}
impl std::fmt::Debug for Proof {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.dbg_fmt(&mut vec![], &mut vec![], f)
  }
}

impl<'a> Parse<'a> for Proof {
  fn parse1(t: &Tree<'a>) -> Self {
    let (tag, attrs, ts) = t.as_tagged();
    match tag {
      0 => {
        let [] = attrs.take_n();
        Proof::Sorry
      }
      1 => {
        let [] = attrs.take_n();
        Proof::Bound(<_>::parse(ts))
      }
      2 => {
        let [x] = attrs.take_n();
        let (y, z) = <_>::parse(ts);
        Proof::AbsT(x, y, z)
      }
      3 => {
        let [x] = attrs.take_n();
        let (y, z) = <_>::parse(ts);
        Proof::AbsP(x, y, z)
      }
      4 => {
        let [] = attrs.take_n();
        let (f, a) = <_>::parse(ts);
        Proof::AppT(f, a)
      }
      5 => {
        let [] = attrs.take_n();
        let (f, a) = <_>::parse(ts);
        Proof::AppP(f, a)
      }
      // 6 => {
      //   let [] = attrs.take_n();
      //   Proof::Hyp(<_>::parse(ts))
      // }
      7 => {
        let [x] = attrs.take_n();
        Proof::Axiom(x, <_>::parse(ts))
      }
      // 8 => {
      //   let [x] = attrs.take_n();
      //   Proof::OfClass(<_>::parse(ts), x)
      // }
      // 9 => {
      //   let [x] = attrs.take_n();
      //   let (t, tys) = <_>::parse(ts);
      //   Proof::Oracle(x, t, tys)
      // }
      10 => {
        let [serial, thy, thm, idx] = attrs.take_n();
        let thm_name = (thm, idx.parse().unwrap());
        // assert!(thm_name == (String::new(), 0));
        Proof::Thm {
          serial: serial.parse().unwrap(),
          theory_name: thy,
          thm_name,
          tyargs: <_>::parse(ts),
        }
      }
      _ => panic!(),
    }
  }
}

#[derive(Debug)]
struct Prop {
  typargs: Vec<(String, Sort)>,
  args: Vec<(String, Box<Type>)>,
  prop: Box<Term>,
}
impl<'a> Parse<'a> for Prop {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (typargs, args, prop) = <_>::parse(t);
    Self { typargs, args, prop }
  }
}

#[derive(Debug)]
struct ProofBox {
  prop: Prop,
  proof: Box<Proof>,
}
impl<'a> Parse<'a> for ProofBox {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (typargs, (args, (prop, proof))) = <_>::parse(t);
    Self { prop: Prop { typargs, args, prop }, proof }
  }
}

impl<'a> Tree<'a> {
  fn as_tagged(&self) -> (usize, VectorIter<'a>, &[Tree<'a>]) {
    let Tree::Elem(name, attrs, ts) = self else { panic!() };
    let tag = std::str::from_utf8(name).unwrap().parse::<usize>().unwrap();
    let attrs = attrs.clone().vector();
    (tag, attrs, ts)
  }

  fn name(&self) -> &'a [u8] {
    match self {
      Tree::Text(_) => panic!(),
      Tree::Elem(name, _, _) => name,
      Tree::Properties(_) | Tree::Node(_) => b":",
    }
  }

  fn as_node(&self) -> &[Tree<'a>] {
    match self {
      Tree::Node(ts) => ts,
      Tree::Properties(attrs) if attrs.is_empty() => &[],
      _ => panic!(),
    }
  }
  fn as_node_n<const N: usize>(&self) -> &[Tree<'a>; N] {
    self.as_node().try_into().unwrap()
  }
}

#[derive(Default)]
struct Properties {
  name: String,
  xname: String,
  pos: (u32, u32),
  label: String,
  file: String,
  id: u32,
  serial: u32,
}
impl Properties {
  fn from_attrs(props: &Attrs<'_>) -> Self {
    let mut this = Self::default();
    for p in props.clone() {
      let (lhs, rhs) = Separated::split(p);
      match lhs {
        b"name" => std::str::from_utf8(rhs).unwrap().clone_into(&mut this.name),
        b"xname" => std::str::from_utf8(rhs).unwrap().clone_into(&mut this.xname),
        b"offset" => this.pos.0 = std::str::from_utf8(rhs).unwrap().parse().unwrap(),
        b"end_offset" => this.pos.1 = std::str::from_utf8(rhs).unwrap().parse().unwrap(),
        b"label" => std::str::from_utf8(rhs).unwrap().clone_into(&mut this.label),
        b"file" => std::str::from_utf8(rhs).unwrap().clone_into(&mut this.file),
        b"id" => this.id = std::str::from_utf8(rhs).unwrap().parse().unwrap(),
        b"serial" => this.serial = std::str::from_utf8(rhs).unwrap().parse().unwrap(),
        _ => panic!(),
      }
    }
    this
  }
}
impl<'a> Parse<'a> for Properties {
  fn parse1(t: &Tree<'a>) -> Self {
    let Tree::Properties(props) = t else { panic!() };
    Self::from_attrs(props)
  }
}

#[derive(Debug)]
struct Entity<T> {
  name: String,
  xname: String,
  pos: (u32, u32),
  label: String,
  file: String,
  id: u32,
  serial: u32,
  val: OptBox<T>,
}
impl<'a, T: Parse<'a>> Parse<'a> for Entity<T> {
  fn parse1_node(this: &Tree<'a>) -> Self {
    let Tree::Elem(b"entity", props, ts) = this else { panic!() };
    let Properties { name, xname, pos, label, file, id, serial } = Properties::from_attrs(props);
    Entity { name, xname, pos, label, file, id, serial, val: <_>::parse(ts) }
  }
}
type Entities<T> = Vec<Entity<T>>;

#[derive(Debug)]
enum Assoc {
  None,
  Left,
  Right,
}
impl<'a> Parse<'a> for Assoc {
  fn parse1(t: &Tree<'a>) -> Self {
    match usize::parse1(t) {
      0 => Assoc::None,
      1 => Assoc::Left,
      2 => Assoc::Right,
      _ => panic!(),
    }
  }
}

#[derive(Debug)]
enum Syntax {
  None,
  Prefix { delim: String },
  Infix { assoc: Assoc, delim: String, prio: usize },
}
impl<'a> Parse<'a> for Syntax {
  fn parse1(t: &Tree<'a>) -> Self {
    let (tag, attrs, ts) = t.as_tagged();
    match tag {
      0 => Syntax::None,
      1 => {
        let [delim] = attrs.take_n();
        Syntax::Prefix { delim }
      }
      2 => {
        let (assoc, delim, prio) = <_>::parse(ts);
        Syntax::Infix { assoc, delim, prio }
      }
      _ => panic!(),
    }
  }
}

#[derive(Debug)]
struct TypeEntry {
  syntax: Syntax,
  args: Vec<String>,
  abbrev: Option<Type>,
}
impl<'a> Parse<'a> for TypeEntry {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (syntax, args, abbrev) = <_>::parse(t);
    Self { syntax, args, abbrev }
  }
}

#[derive(Debug)]
struct ConstEntry {
  syntax: Syntax,
  args: Vec<String>,
  ty: Type,
  abbrev: Option<Term>,
  propositional: bool,
}
impl<'a> Parse<'a> for ConstEntry {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (syntax, (args, (ty, (abbrev, propositional)))) = <_>::parse(t);
    Self { syntax, args, ty, abbrev, propositional }
  }
}

#[derive(Debug)]
enum AxiomReason {
  Forgot,
  Axiom,
  Prim,
  Def { unchecked: bool, overloaded: bool },
  ClassRel,
  Arity,
}
impl<'a> Parse<'a> for AxiomReason {
  fn parse1(t: &Tree<'a>) -> Self {
    let (tag, _, ts) = t.as_tagged();
    match tag {
      0 => Self::Forgot,
      1 => Self::Axiom,
      2 => Self::Prim,
      3 => {
        let (unchecked, overloaded) = <_>::parse(ts);
        Self::Def { unchecked, overloaded }
      }
      4 => Self::ClassRel,
      5 => Self::Arity,
      _ => panic!(),
    }
  }
}

type AxiomEntry = (Prop, AxiomReason);

#[derive(Debug)]
struct ThmEntry {
  proof: ProofBox,
  deps: Vec<(String, usize)>,
}
impl<'a> Parse<'a> for ThmEntry {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (prop, deps, proof) = <_>::parse(t);
    Self { proof: ProofBox { prop, proof }, deps }
  }
}

#[derive(Debug)]
enum Recursion {
  PrimRec(Vec<String>),
  Rec,
  PrimCorec(Vec<String>),
  Corec,
  Unknown,
}
impl<'a> Parse<'a> for Recursion {
  fn parse1(t: &Tree<'a>) -> Self {
    let (tag, _, ts) = t.as_tagged();
    match tag {
      0 => Self::PrimRec(<_>::parse(ts)),
      1 => Self::Rec,
      2 => Self::PrimCorec(<_>::parse(ts)),
      3 => Self::Corec,
      4 => Self::Unknown,
      _ => panic!(),
    }
  }
}

#[derive(Debug)]
enum RoughClassification {
  Equational(Recursion),
  Inductive,
  Coinductive,
  Unknown,
}
impl<'a> Parse<'a> for RoughClassification {
  fn parse1(t: &Tree<'a>) -> Self {
    let (tag, _, ts) = t.as_tagged();
    match tag {
      0 => Self::Equational(<_>::parse(ts)),
      1 => Self::Inductive,
      2 => Self::Coinductive,
      3 => Self::Unknown,
      _ => panic!(),
    }
  }
}

#[derive(Debug)]
struct SpecRule {
  name: String,
  pos: (u32, u32),
  label: String,
  file: String,
  id: u32,
  class: RoughClassification,
  typargs: Vec<(String, Sort)>,
  args: Vec<(String, Box<Type>)>,
  terms: Vec<(Box<Term>, Box<Type>)>,
  rules: Vec<Term>,
}
impl<'a> Parse<'a> for SpecRule {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (
      Properties { pos, label, file, id, .. },
      (name, (class, (typargs, (args, (terms, rules))))),
    ) = <_>::parse(t);
    Self { pos, label, file, id, name, class, typargs, args, terms, rules }
  }
}

#[derive(Debug)]
struct ClassEntry {
  params: Vec<(String, Box<Type>)>,
  axioms: Vec<AxiomEntry>,
}
impl<'a> Parse<'a> for ClassEntry {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (params, axioms) = <_>::parse(t);
    Self { params, axioms }
  }
}

#[derive(Debug)]
struct ClassRelEntry {
  c1: String,
  c2: String,
  prop: Prop,
}
impl<'a> Parse<'a> for ClassRelEntry {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (prop, (c1, c2)) = <_>::parse(t);
    Self { c1, c2, prop }
  }
}

#[derive(Debug)]
struct Arity {
  type_name: String,
  domain: Vec<Sort>,
  codomain: String,
  prop: Prop,
}
impl<'a> Parse<'a> for Arity {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (prop, (type_name, domain, codomain)) = <_>::parse(t);
    Self { type_name, domain, codomain, prop }
  }
}

#[derive(Debug)]
struct LocaleArg {
  name: String,
  ty: Box<Type>,
  syntax: Syntax,
}
impl<'a> Parse<'a> for LocaleArg {
  fn parse(t: &[Tree<'a>]) -> Self {
    let ((name, ty), syntax) = <_>::parse(t);
    Self { name, ty, syntax }
  }
}

#[derive(Debug)]
struct LocaleEntry {
  typargs: Vec<(String, Sort)>,
  args: Vec<LocaleArg>,
  axioms: Vec<Prop>,
}
impl<'a> Parse<'a> for LocaleEntry {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (typargs, args, axioms) = <_>::parse(t);
    Self { typargs, args, axioms }
  }
}

#[derive(Debug)]
struct LocaleDepEntry {
  source: String,
  target: String,
  prefix: Vec<(String, bool)>,
  subst_types: Vec<((String, Sort), Box<Type>)>,
  subst_terms: Vec<((String, Box<Type>), Box<Term>)>,
}
impl<'a> Parse<'a> for LocaleDepEntry {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (source, (target, (prefix, (subst_types, subst_terms)))) = <_>::parse(t);
    Self { source, target, prefix, subst_types, subst_terms }
  }
}

#[derive(Debug)]
struct ConstDef {
  name: String,
  axiom: String,
}
impl<'a> Parse<'a> for ConstDef {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (name, axiom) = <_>::parse(t);
    Self { name, axiom }
  }
}

#[derive(Debug)]
struct TypeDef {
  name: String,
  rep_ty: Box<Type>,
  abs_ty: Box<Type>,
  rep: String,
  abs: String,
  axiom: String,
}
impl<'a> Parse<'a> for TypeDef {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (name, (rep_ty, (abs_ty, (rep, (abs, axiom))))) = <_>::parse(t);
    Self { name, rep_ty, abs_ty, rep, abs, axiom }
  }
}

#[derive(Debug)]
struct Datatype {
  name: String,
  pos: (u32, u32),
  label: String,
  file: String,
  id: u32,
  co: bool,
  typargs: Vec<(String, Sort)>,
  typ: Box<Type>,
  ctors: Vec<(Box<Term>, Box<Type>)>,
}
impl<'a> Parse<'a> for Datatype {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (Properties { pos, label, file, id, .. }, (name, (co, (typargs, (typ, ctors))))) =
      <_>::parse(t);
    Self { name, pos, label, file, id, co, typargs, typ, ctors }
  }
}

#[derive(Default)]
struct Session {
  types: Vec<(String, Entities<TypeEntry>)>,
  consts: Vec<(String, Entities<ConstEntry>)>,
  axioms: Vec<(String, Entities<AxiomEntry>)>,
  thms: Vec<(String, Entities<ThmEntry>)>,
  classes: Vec<(String, Entities<ClassEntry>)>,
  locales: Vec<(String, Entities<LocaleEntry>)>,
  other: Vec<(String, String, Entities<()>)>,
  const_defs: Vec<(String, Vec<ConstDef>)>,
  spec_rules: Vec<(String, Vec<SpecRule>)>,
  class_rels: Vec<(String, Vec<ClassRelEntry>)>,
  arities: Vec<(String, Vec<Arity>)>,
  locale_deps: Vec<(String, Entities<LocaleDepEntry>)>,
  type_defs: Vec<(String, Vec<TypeDef>)>,
  datatypes: Vec<(String, Vec<Datatype>)>,
  parents: Vec<String>,
}

struct Axiom {
  sess: &'static str,
  i: u32,
  j: u32,
}

#[derive(Default)]
pub struct Global {
  proofs: HashMap<u32, ProofBox>,
  traces: HashMap<u32, ThmTrace>,
  axioms: HashMap<String, Axiom>,
}

impl Global {
  fn load_session(&mut self, sess: &'static str, proofs: bool) -> Result<Box<Session>> {
    let path = format!("/home/mario/.isabelle/heaps/polyml-5.9.1_x86_64_32-linux/log/{sess}.db");
    let file = Path::new(&path);
    assert!(file.exists(), "could not find {:?}", sess);
    let db = Connection::open(file)?;
    let mut q = db.prepare("select * from isabelle_exports")?;
    let mut rows = q.query(())?;
    let mut data = Box::new(Session::default());
    while let Some(row) = rows.next()? {
      #[derive(Debug)]
      enum RowType<'a> {
        Proof(u32),
        Trace(u32),
        Types(&'a str),
        Consts(&'a str),
        Axioms(&'a str),
        Thms(&'a str),
        Classes(&'a str),
        ClassRels(&'a str),
        Arities(&'a str),
        Locales(&'a str),
        LocaleDeps(&'a str),
        ConstDefs(&'a str),
        SpecRules(&'a str),
        TypeDefs(&'a str),
        Datatypes(&'a str),
        Other(&'a str, &'a str),
      }
      let name = {
        let s = row.get_ref(2)?.as_str()?;
        if let Some(s) = s.strip_prefix("proofs/") {
          if !proofs {
            continue;
          }
          RowType::Proof(s.parse().unwrap())
        } else if let Some(s) = s.strip_prefix("proof_trace/") {
          if !proofs {
            continue;
          }
          RowType::Trace(s.parse().unwrap())
        } else {
          let theory = row.get_ref(1)?.as_str()?;
          if let Some(s) = s.strip_prefix("theory/other/") {
            RowType::Other(theory, s)
          } else {
            match s {
              "theory/types" => RowType::Types(theory),
              "theory/consts" => RowType::Consts(theory),
              "theory/axioms" => RowType::Axioms(theory),
              "theory/thms" => RowType::Thms(theory),
              "theory/classes" => RowType::Classes(theory),
              "theory/locales" => RowType::Locales(theory),
              "theory/locale_dependencies" => RowType::LocaleDeps(theory),
              "theory/classrel" => RowType::ClassRels(theory),
              "theory/arities" => RowType::Arities(theory),
              "theory/constdefs" => RowType::ConstDefs(theory),
              "theory/spec_rules" => RowType::SpecRules(theory),
              "theory/typedefs" => RowType::TypeDefs(theory),
              "theory/datatypes" => RowType::Datatypes(theory),
              "theory/parents" => {
                for s in std::str::from_utf8(row.get_ref(5)?.as_blob()?).unwrap().lines() {
                  data.parents.push(s.trim().to_owned())
                }
                continue;
              }
              _ => continue,
            }
          }
        }
      };
      let mut out;
      let blob = row.get_ref(5)?.as_blob()?;
      let blob = if row.get(4)? {
        out = vec![];
        let reader = std::io::Cursor::new(blob);
        zstd::stream::Decoder::new(reader).unwrap().read_to_end(&mut out).unwrap();
        &out
      } else {
        blob
      };
      let blob = parse(blob);
      match name {
        RowType::Proof(i) => {
          self.proofs.insert(i, ProofBox::parse(&blob));
        }
        RowType::Trace(i) => {
          self.traces.insert(i, ThmTrace::parse_v2(&Tree::Node(blob)));
        }
        RowType::Types(theory) => data.types.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Consts(theory) => data.consts.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Axioms(theory) => data.axioms.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Thms(theory) => {
          let mut thms = Entities::parse(&blob);
          if !proofs {
            for e in &mut thms {
              e.val.0.take();
            }
          }
          data.thms.push((theory.to_owned(), thms));
        }
        RowType::ConstDefs(theory) => data.const_defs.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::SpecRules(theory) => data.spec_rules.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Classes(theory) => data.classes.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::ClassRels(theory) => data.class_rels.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Arities(theory) => data.arities.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Locales(theory) => data.locales.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::LocaleDeps(theory) => {
          data.locale_deps.push((theory.to_owned(), <_>::parse(&blob)))
        }
        RowType::TypeDefs(theory) => data.type_defs.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Datatypes(theory) => data.datatypes.push((theory.to_owned(), <_>::parse(&blob))),
        RowType::Other(theory, kind) => {
          data.other.push((theory.to_owned(), kind.to_owned(), <_>::parse(&blob)))
        }
      }
    }
    Ok(data)
  }
}

lalrpop_mod!(root);

fn main() -> Result<()> {
  let isabelle_root = std::path::PathBuf::from("/home/mario/Documents/isabelle");
  let p = root::EntriesParser::new();
  let main = &*std::env::args().nth(1).unwrap().leak();
  let mut g = Global::default();
  let mut stack = vec![];
  {
    let mut parents: HashMap<String, Option<String>> = Default::default();
    for root in std::fs::read_to_string(isabelle_root.join("ROOTS")).unwrap().lines() {
      let s = std::fs::read_to_string(isabelle_root.join(root).join("ROOT")).unwrap();
      for e in p.parse(&s).unwrap() {
        if let Entry::Session { sess, parent } = e {
          parents.insert(sess.into(), parent.map(String::from));
        }
      }
    }
    let mut sess = main;
    while let Some(i) = &parents[sess] {
      stack.push(&*i.to_owned().leak());
      sess = i;
    }
  }
  let mut parents = vec![];
  for sess in stack.iter().rev() {
    parents.push((*sess, g.load_session(sess, false)?));
  }
  let sess = g.load_session(main, true)?;
  for (name, sess) in parents.iter().map(|(x, y)| (*x, y)).chain(std::iter::once((main, &sess))) {
    for (i, (_, axioms)) in sess.axioms.iter().enumerate() {
      let i = i as u32;
      for (j, e) in axioms.iter().enumerate() {
        let j = j as u32;
        assert!(g.axioms.insert(e.name.clone(), Axiom { sess: name, i, j }).is_none());
      }
    }
  }
  for (name, sess) in parents.iter().map(|(x, y)| (*x, y)).chain(std::iter::once((main, &sess))) {
    for (i, (_, const_defs)) in sess.const_defs.iter().enumerate() {
      let i = i as u32;
      for (j, e) in const_defs.iter().enumerate() {
        let j = j as u32;
        println!("const_def {}: {}", e.name, e.axiom);
        // assert!(g.axioms.insert(e.name.clone(), Axiom { sess: name, i, j }).is_none());
      }
    }
  }
  for (name, sess) in parents.iter().map(|(x, y)| (*x, y)).chain(std::iter::once((main, &sess))) {
    for (theory, entities) in &sess.types {
      for entity in entities {
        println!("{theory} type: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.consts {
      for entity in entities {
        println!("{theory} const: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.axioms {
      for entity in entities {
        println!("{theory} axiom: {}", entity.name);
        if let Some(x) = &entity.val.0 {
          println!("  = {:?}", x.1)
        }
      }
    }
    for (theory, entities) in &sess.thms {
      for entity in entities {
        println!("{theory} thm: {}", entity.name);
        // if let Some(s) = g.proofs.get(&entity.serial) {
        //   println!("=> {:#?}", s)
        // }
        // if let Some(s) = g.traces.get(&entity.serial) {
        //   println!("=> {:#?}", s)
        // }
      }
    }
    for (theory, entities) in &sess.classes {
      for entity in entities {
        println!("{theory} class: {}", entity.name);
        if let Some(x) = &entity.val.0 {
          println!("  = {:?}", x)
        } else {
          println!("  = none")
        }
      }
    }
    for (theory, entities) in &sess.locales {
      for entity in entities {
        println!("{theory} locale: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.class_rels {
      for entity in entities {
        println!("{theory} class_rel: {} -> {}", entity.c1, entity.c2)
      }
    }
    for (theory, entities) in &sess.arities {
      for entity in entities {
        println!("{theory} arity: {}", entity.type_name)
      }
    }
    for (theory, kind, entities) in &sess.other {
      for entity in entities {
        println!("{theory} {kind}: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.const_defs {
      for entity in entities {
        println!("{theory} const_def: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.spec_rules {
      for entity in entities {
        println!("{theory} spec_rule: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.locale_deps {
      for entity in entities {
        println!("{theory} locale_dep: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.type_defs {
      for entity in entities {
        println!("{theory} type_def: {}", entity.name)
      }
    }
    for (theory, entities) in &sess.datatypes {
      for entity in entities {
        println!("{theory} datatype: {}", entity.name)
      }
    }
  }
  let mut gthms: HashMap<u32, (usize, usize, usize)> = Default::default();
  for (i, (_, sess)) in parents.iter().enumerate() {
    for (j, (_, thms)) in sess.thms.iter().enumerate() {
      for (k, thm) in thms.iter().enumerate() {
        gthms.insert(thm.serial, (i, j, k));
      }
    }
  }
  // for (&i, p) in &g.proofs {
  //   println!("proofs/{i}: {p:#?}")
  // }
  #[derive(Debug)]
  enum Uses {
    Once,
    Multiple,
    Public,
  }
  let mut uses: HashMap<u32, Uses> = Default::default();
  {
    let mut queue: Vec<u32> = vec![];
    for (_, e) in &sess.thms {
      for entity in e {
        if g.traces.contains_key(&entity.serial) {
          uses.insert(entity.serial, Uses::Public);
          queue.push(entity.serial);
        }
      }
    }
    let mut reachable: HashSet<u32> = Default::default();
    while let Some(i) = queue.pop() {
      if reachable.insert(i) {
        for pr in &g.traces[&i].ctx.proofs.0 {
          if let &trace::Proof::Thm(j) = pr {
            if !gthms.contains_key(&j) {
              match uses.entry(j) {
                std::collections::hash_map::Entry::Occupied(mut e) => {
                  if let Uses::Once = *e.get() {
                    e.insert(Uses::Multiple);
                  }
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                  e.insert(Uses::Once);
                }
              }
              queue.push(j)
            }
          }
        }
      }
    }
  }
  for entity in sess.axioms.iter().flat_map(|(_, x)| x) {
    match entity.val.0.as_deref() {
      None => panic!("axiom {} not exported", entity.name),
      Some((_, AxiomReason::Forgot)) => panic!("axiom missing provenance"),
      Some((_, AxiomReason::Def { unchecked: false, overloaded: false })) => {
        // todo: definition checking
      }
      Some((_, AxiomReason::Axiom)) => {
        println!("user axiom {}: {:?}", entity.name, entity.val.0.as_deref().unwrap().0.prop)
      }
      Some((_, AxiomReason::Prim)) => {
        assert!(matches!(
          &*entity.name,
          "Pure.reflexive"
            | "Pure.symmetric"
            | "Pure.transitive"
            | "Pure.equal_intr"
            | "Pure.equal_elim"
            | "Pure.abstract_rule"
            | "Pure.combination"
        ))
      }
      Some((_, r)) => todo!("reason: {r:?}"),
    }
  }
  let mut v = uses.iter().filter(|x| !matches!(x.1, Uses::Once)).map(|x| *x.0).collect::<Vec<_>>();
  v.sort();
  for i in v {
    let p = &g.traces[&i];
    println!(
      "proof_trace/{i} = {:?}.{} -> {:?}",
      p.ctx.strings[p.header.thm_name.name],
      p.header.thm_name.i,
      uses.get(&i),
    );
    Checker::new(&bumpalo::Bump::new(), &g).check(p);
  }
  // for (i, p) in &g.traces {
  //   p.root.0.thm_name.name
  // }
  Ok(())
}
