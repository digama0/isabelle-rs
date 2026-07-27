#![allow(unused)]
use aligned_vec::{ABox, AVec, ConstAlign};
use ast::Entry;
use binparser::{BinParser, TagPtr};
use itertools::Itertools;
use kernel::Checker;
use lalrpop_util::lalrpop_mod;
use rusqlite::{Connection, Result};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::io::Read;
use std::path::Path;
use trace::ThmTrace;

pub mod ast;
pub mod binparser;
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
      Self::Text(s) => write!(f, "{:?}", String::from_utf8_lossy(s)),
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
const Z: u8 = 251;

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

/// Reinterpret a 4-aligned byte buffer as the `u32` words of a `PolyML.exportSmall` image.
fn into_words(out: AVec<u8, ConstAlign<4>>) -> Box<[u32]> {
  let out = out.into_boxed_slice();
  assert!(out.len() % 4 == 0, "truncated image");
  unsafe {
    let ptr = ABox::into_raw_parts(out).0;
    let ptr = std::ptr::slice_from_raw_parts_mut(ptr as *mut u32, ptr.len() / 4);
    Box::from_raw(ptr)
  }
}

/// `proof_trace_raw/*` rows (v11): the image is streamed to the database verbatim by
/// `PolyML.exportSmallToFD`, so there is no YXML wrapper and nothing to unescape --
/// only the copy into an aligned buffer remains.
fn to_words(bytes: &[u8]) -> Box<[u32]> {
  let mut out = AVec::<u8, ConstAlign<4>>::new(4);
  out.extend_from_slice(bytes);
  into_words(out)
}

/// `proof_trace/*` rows (v10): the image went through `YXML.escape`, so bytes 5/6/251
/// arrive escaped behind 251.
fn unescape(mut bytes: &[u8]) -> Box<[u32]> {
  let mut out = AVec::<u8, ConstAlign<4>>::new(4);
  while let Some(i) = memchr::memchr(Z, bytes) {
    out.extend_from_slice(&bytes[..i]);
    out.push(match bytes.get(i + 1) {
      Some(0) => X,
      Some(1) => Y,
      Some(2) => Z,
      _ => panic!("bad escape"),
    });
    bytes = &bytes[i + 2..]
  }
  out.extend_from_slice(bytes);
  into_words(out)
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

#[derive(Clone)]
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

#[derive(Clone)]
enum Term {
  #[allow(clippy::enum_variant_names)]
  Const(String, Vec<Type>),
  Const2(String, Box<Type>),
  Free(String, Option<Box<Type>>),
  Var(String, u32, Option<Box<Type>>),
  Bound(u32),
  Abs(String, Box<Type>, Box<Term>),
  App(Box<Term>, Box<Term>),
  /// `OFCLASS(T, c)`: the payload is a *type*, which is why a nullary type constructor
  /// used to parse as a `Const` by accident
  OfClass(String, Box<Type>),
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
      Term::OfClass(c, ty) => write!(f, "OfClass({}, {ty:?})", short_name(c)),
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
#[derive(Clone)]
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
  Typedef,
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
      6 => Self::Typedef,
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
  /// `encode_class` writes the class axioms as bare propositions -- unlike `theory/axioms`,
  /// there is no provenance attached
  axioms: Vec<Prop>,
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
  #[allow(clippy::type_complexity)]
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

/// An exported proof trace, still in the form it has in the session database.
struct Trace {
  compressed: bool,
  /// `proof_trace_raw/*` (v11, streamed via `exportSmallToFD`) rather than the
  /// YXML-escaped `proof_trace/*` of v10.
  raw: bool,
  data: Box<[u8]>,
}

impl Trace {
  fn decode(&self) -> Box<[u32]> {
    let data = maybe_decompress(self.compressed, &self.data);
    if self.raw {
      to_words(&data)
    } else {
      let [Tree::Text(blob)] = *parse(&data) else { panic!("expected a single text node") };
      unescape(blob)
    }
  }
}

#[derive(Default)]
pub struct Global {
  proofs: HashMap<u32, ProofBox>,
  traces: HashMap<u32, Trace>,
  axioms: HashMap<String, Axiom>,
  /// what each *checked* theorem proves, so that a citation of it (`Thm`, `ConstrainThm`)
  /// can be verified rather than trusted.  Terms are interned per theorem, so the
  /// statement is kept as a tree and reified into whichever checker needs it.
  pub verified: HashMap<u32, VerifiedThm>,
  /// theorems belonging to a parent session, which this run does not re-check: a citation
  /// of one has to be taken on trust
  pub external: HashSet<u32>,
  /// the theory's class algebra: `Sorts.algebra` as the checker needs it
  pub classes: ClassAlgebra,
  /// declared constants: name ↦ (its type argument names, its type)
  pub(crate) consts: HashMap<String, (Vec<String>, Type)>,
  /// declared type constructors: name ↦ arity
  pub types: HashMap<String, usize>,
  /// what each axiom states, so that a trace citing one by name can be held to it
  pub(crate) axiom_props: HashMap<String, Prop>,
}

/// `Sorts.algebra`, in the form `Sorts.of_sort` needs: the class inclusions, closed under
/// transitivity, and the arities, completed under those inclusions the way
/// `insert_complete_ars` does.
#[derive(Default)]
pub struct ClassAlgebra {
  /// class ↦ that class and everything it entails
  pub supers: HashMap<String, HashSet<String>>,
  /// (type constructor, class) ↦ the argument sorts a type of that class must have
  pub arities: HashMap<(String, String), Vec<Vec<String>>>,
}

impl ClassAlgebra {
  /// `Sorts.class_le`
  pub fn class_le(&self, c1: &str, c2: &str) -> bool {
    c1 == c2 || self.supers.get(c1).is_some_and(|s| s.contains(c2))
  }

  /// `Sorts.sort_le`: every class of `s2` is entailed by some class of `s1`
  pub fn sort_le(&self, s1: &[String], s2: &[String]) -> bool {
    s2.iter().all(|c2| s1.iter().any(|c1| self.class_le(c1, c2)))
  }

  fn add_classrel(&mut self, c1: &str, c2: &str) {
    self.supers.entry(c1.to_owned()).or_default().insert(c2.to_owned());
    self.supers.entry(c2.to_owned()).or_default();
  }

  /// transitive closure of the class inclusions, then `complete`/`insert` of the declared
  /// arities: an arity for `c` is also an arity for every superclass of `c`, and where two
  /// candidates for the same `(t, c)` are comparable the *weaker* domain wins (a more
  /// general arity), which is what `Sorts.insert` keeps
  fn close(&mut self, arities: Vec<(String, Vec<Vec<String>>, String)>) {
    let keys: Vec<String> = self.supers.keys().cloned().collect();
    loop {
      let mut changed = false;
      for c in &keys {
        let mut sup = self.supers[c].clone();
        let n = sup.len();
        for d in self.supers[c].clone() {
          if let Some(s) = self.supers.get(&d) {
            sup.extend(s.iter().cloned())
          }
        }
        if sup.len() != n {
          changed = true;
          self.supers.insert(c.clone(), sup);
        }
      }
      if !changed {
        break
      }
    }
    for (t, dom, c) in arities {
      let mut cs = vec![c.clone()];
      cs.extend(self.supers.get(&c).into_iter().flatten().cloned());
      for c in cs {
        let key = (t.clone(), c);
        match self.arities.get(&key) {
          None => {
            self.arities.insert(key, dom.clone());
          }
          Some(old) => {
            // keep the more general domain, as `Sorts.insert` does
            let old = old.clone();
            let new_is_weaker =
              old.len() == dom.len() && (old.iter().zip(&dom)).all(|(a, b)| self.sort_le(a, b));
            if new_is_weaker {
              self.arities.insert(key, dom.clone());
            }
          }
        }
      }
    }
  }
}

/// The statement a checked theorem was verified against, in the `unconstrainT`-ed form the
/// exporter records: `⟦OFCLASS(?'a, c); …⟧ ⟹ prop`, with the map from the theorem's own
/// type variables to the stripped ones.
///
/// Kept as a flat encoding rather than a term tree: a session has hundreds of thousands of
/// these live at once (a theorem is only dropped when nothing can cite it any more), and a
/// tree of `String`-carrying nodes costs two orders of magnitude more.
/// a node of the definitional dependency graph: a constant, plus the head constructors of
/// its type arguments so that overloaded definitions are kept apart
type DefNode = (String, Vec<Option<String>>);

struct Definition {
  lhs: DefNode,
  rhs: Vec<DefNode>,
}

/// `Theory.add_def`'s conditions on a definitional axiom: it equates a constant (applied to
/// distinct variables) with a right-hand side that introduces nothing new -- no free
/// variables beyond the arguments, no type variables beyond the constant's.
fn check_definition(g: &Global, prop: &Prop) -> Result<Definition, String> {
  fn head_of(ty: &Type) -> Option<String> {
    match ty {
      Type::Type(c, _) => Some(c.clone()),
      _ => None,
    }
  }
  fn node(c: &str, tyargs: &[Type]) -> DefNode {
    (c.to_owned(), tyargs.iter().map(head_of).collect())
  }
  fn consts_of(t: &Term, out: &mut Vec<DefNode>, frees: &mut Vec<String>) {
    match t {
      Term::Const(c, tyargs) => out.push(node(c, tyargs)),
      Term::Const2(c, _) => out.push((c.clone(), vec![])),
      Term::Free(x, _) => frees.push(x.clone()),
      Term::Var(x, _, _) => frees.push(x.clone()),
      Term::Abs(_, _, e) => consts_of(e, out, frees),
      Term::App(f, u) => {
        consts_of(f, out, frees);
        consts_of(u, out, frees)
      }
      _ => {}
    }
  }
  // `⋀`/`Trueprop` wrappers, then the equation
  let mut t = &*prop.prop;
  loop {
    match t {
      Term::App(f, u) => match &**f {
        Term::Const(c, _) | Term::Const2(c, _) if c == "HOL.Trueprop" || c == "Pure.prop" => t = u,
        _ => break,
      },
      _ => break,
    }
  }
  let Term::App(f, rhs) = t else { return Err("not an equation".into()) };
  let Term::App(eq, lhs) = &**f else { return Err("not an equation".into()) };
  match &**eq {
    Term::Const(c, _) | Term::Const2(c, _) if c == "Pure.eq" || c == "HOL.eq" => {}
    _ => return Err("not an equation".into()),
  }
  // the left-hand side: a constant applied to distinct variables
  let mut args = vec![];
  // a class definition takes its type argument as `TYPE('a)`, which `Logic.dest_def` treats
  // as a type argument rather than a term one
  let mut type_args = vec![];
  let mut head = &**lhs;
  while let Term::App(f, u) = head {
    match &**u {
      Term::Free(x, _) | Term::Var(x, _, _) => args.push(x.clone()),
      Term::Const(c, tys) if c == "Pure.type" => match &tys[..] {
        [Type::Free(x, _) | Type::Var(x, _, _)] => type_args.push(x.clone()),
        _ => return Err("TYPE argument is not a type variable".into()),
      },
      other => return Err(format!("left-hand side argument is not a variable: {other:?}")),
    }
    head = f
  }
  let (c, tyargs) = match head {
    Term::Const(c, tyargs) => (c.clone(), tyargs.clone()),
    Term::Const2(c, _) => (c.clone(), vec![]),
    // `Axclass.define_class` defines the class predicate, which the export writes as an
    // `OFCLASS` rather than as the constant `c_class` it is
    Term::OfClass(c, ty) => (format!("{c}_class"), vec![(**ty).clone()]),
    _ => return Err("left-hand side is not a constant".into()),
  };
  {
    let mut seen = HashSet::new();
    if !args.iter().all(|a| seen.insert(a.clone())) {
      return Err("repeated argument on the left-hand side".into())
    }
    let mut seen = HashSet::new();
    if !type_args.iter().all(|a| seen.insert(a.clone())) {
      return Err("repeated TYPE argument on the left-hand side".into())
    }
  }
  if !g.consts.contains_key(&c) {
    return Err(format!("defines undeclared constant {c}"))
  }
  // the right-hand side introduces nothing new
  let (mut rhs_consts, mut rhs_frees) = (vec![], vec![]);
  consts_of(rhs, &mut rhs_consts, &mut rhs_frees);
  if let Some(x) = rhs_frees.iter().find(|x| !args.contains(x)) {
    return Err(format!("right-hand side has a free variable {x}"))
  }
  let mut lhs_tvars = type_args.clone();
  for ty in &tyargs {
    tvars_of(ty, &mut lhs_tvars)
  }
  let mut rhs_tvars = vec![];
  tvars_of_term(rhs, &mut rhs_tvars);
  if let Some(x) = rhs_tvars.iter().find(|x| !lhs_tvars.contains(x)) {
    return Err(format!("right-hand side has a type variable {x} the constant does not"))
  }
  Ok(Definition { lhs: node(&c, &tyargs), rhs: rhs_consts })
}

fn tvars_of(ty: &Type, out: &mut Vec<String>) {
  match ty {
    Type::Type(_, args) => args.iter().for_each(|a| tvars_of(a, out)),
    Type::Free(x, _) | Type::Var(x, _, _) => {
      if !out.contains(x) {
        out.push(x.clone())
      }
    }
  }
}

fn tvars_of_term(t: &Term, out: &mut Vec<String>) {
  match t {
    Term::Const(_, tys) => tys.iter().for_each(|a| tvars_of(a, out)),
    Term::Const2(_, ty) => tvars_of(ty, out),
    Term::Free(_, Some(ty)) => tvars_of(ty, out),
    Term::Var(_, _, Some(ty)) => tvars_of(ty, out),
    Term::Abs(_, ty, e) => {
      tvars_of(ty, out);
      tvars_of_term(e, out)
    }
    Term::App(f, u) => {
      tvars_of_term(f, out);
      tvars_of_term(u, out)
    }
    Term::OfClass(_, ty) => tvars_of(ty, out),
    _ => {}
  }
}

pub struct VerifiedThm {
  /// the names this statement mentions, indexed by the encoding
  pub strings: Vec<String>,
  pub buf: Vec<u8>,
  /// `-1` for a promise trace (see `ThmTrace::unconstrain_shyps`)
  pub n_ofclass: i32,
}

fn maybe_decompress(compressed: bool, blob: &[u8]) -> Cow<'_, [u8]> {
  if compressed {
    let mut out = vec![];
    let reader = std::io::Cursor::new(blob);
    zstd::stream::Decoder::new(reader).unwrap().read_to_end(&mut out).unwrap();
    Cow::Owned(out)
  } else {
    Cow::Borrowed(blob)
  }
}

impl Global {
  fn load_session(&mut self, sess: &'static str, proofs: bool) -> Result<Box<Session>> {
    let path =
      format!("/home/mario/.isabelle/heaps/polyml-exportSmall_x86_64_32-linux/log/{sess}.db");
    let file = Path::new(&path);
    assert!(file.exists(), "could not find {:?}", sess);
    let db = Connection::open(file)?;
    let mut q = db.prepare("select * from isabelle_exports")?;
    let mut rows = q.query(())?;
    let mut data = Box::new(Session::default());
    let mut warned: HashSet<String> = Default::default();
    while let Some(row) = rows.next()? {
      #[derive(Debug)]
      enum RowType<'a> {
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
        let raw = s.strip_prefix("proof_trace_raw/");
        if let Some(s) = raw.or_else(|| s.strip_prefix("proof_trace/")) {
          self.traces.insert(
            s.parse().unwrap(),
            Trace {
              compressed: row.get(4)?,
              raw: raw.is_some(),
              data: row.get_ref(5)?.as_blob()?.to_vec().into_boxed_slice(),
            },
          );
          continue;
        }
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
              let blob = maybe_decompress(row.get(4)?, row.get_ref(5)?.as_blob()?);
              for s in std::str::from_utf8(&blob).unwrap().lines() {
                data.parents.push(s.trim().to_owned())
              }
              continue;
            }
            _ => continue,
          }
        }
      };
      let blob = maybe_decompress(row.get(4)?, row.get_ref(5)?.as_blob()?);
      let blob = parse(&blob);
      if std::env::var_os("SHOW_ROWS").is_some() {
        eprintln!("row {name:?}");
      }
      // The checker consumes a handful of export kinds; the rest are parsed only because
      // they are there, and their formats drift.  A parse failure in one of those is a
      // warning, not the end of the run -- but the ones the checker relies on stay strict.
      let essential = matches!(
        name,
        RowType::Axioms(_)
          | RowType::Thms(_)
          | RowType::Classes(_)
          | RowType::ClassRels(_)
          | RowType::Arities(_)
      );
      let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      match name {
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
        RowType::ClassRels(theory) => {
          data.class_rels.push((theory.to_owned(), <_>::parse(&blob)))
        }
        RowType::Arities(theory) => {
          data.arities.push((theory.to_owned(), <_>::parse(&blob)))
        }
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
      }));
      if parsed.is_err() {
        assert!(!essential, "cannot parse {name:?}");
        if warned.insert(format!("{name:?}").split('(').next().unwrap_or("").to_owned()) {
          eprintln!("warning: cannot parse {name:?}, ignoring this export kind")
        }
      }
    }
    Ok(data)
  }
}

lalrpop_mod!(root);

thread_local! {
  /// filled in by the panic hook, read back by `catch_unwind`
  static LAST_PANIC: std::cell::RefCell<(String, String)> =
    std::cell::RefCell::new((String::new(), String::new()));
}

fn main() -> Result<()> {
  // the checker recurses over terms (reification, eta expansion, sort checks), and HOL has
  // terms deep enough to overflow the default 8M stack
  std::thread::Builder::new()
    .stack_size(1 << 30)
    .spawn(run)
    .expect("spawn")
    .join()
    .expect("checker thread")
}

fn run() -> Result<()> {
  // record panics instead of printing them: the driver keeps going and reports a summary
  std::panic::set_hook(Box::new(|info| {
    let msg = info
      .payload()
      .downcast_ref::<String>()
      .cloned()
      .or_else(|| info.payload().downcast_ref::<&str>().map(|s| (*s).to_owned()))
      .unwrap_or_else(|| "?".to_owned());
    let loc = info.location().map_or_else(String::new, |l| format!("{}:{}", l.file(), l.line()));
    if std::env::var_os("SHOW_PANIC").is_some() {
      eprintln!("panicked at {loc}: {msg}\n{}", std::backtrace::Backtrace::force_capture());
    }
    LAST_PANIC.with(|p| *p.borrow_mut() = (msg, loc));
  }));
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
  {
    // the class algebra of the session and everything it builds on
    let mut arities = vec![];
    let mut n_exported = 0usize;
    for sess in parents.iter().map(|(_, y)| y).chain(std::iter::once(&sess)) {
      for e in sess.class_rels.iter().flat_map(|(_, x)| x) {
        g.classes.add_classrel(&e.c1, &e.c2)
      }
      for (_, entities) in &sess.classes {
        for e in entities {
          g.classes.supers.entry(e.name.clone()).or_default();
        }
      }
      for e in sess.arities.iter().flat_map(|(_, x)| x) {
        n_exported += 1;
        arities.push((e.type_name.clone(), e.domain.clone(), e.codomain.clone()))
      }
      // `theory/classrel` and `theory/arities` are only written for what
      // `Sorts.dest_algebra` reports as new in a theory, which in practice is nothing: the
      // facts arrive as *axioms* tagged `ClassRel`/`Arity`, in the `unconstrainT`-ed form
      // where the sorts of the type variables have become `OFCLASS` premises.
      // Arities and class relations reach us as facts of the form
      // `⟦OFCLASS(?'a, c1); …⟧ ⟹ OFCLASS(T, c)`: either axioms tagged `Arity`/`ClassRel`,
      // or *theorems* (an `instance` proof), which this run checks like any other.
      // not only the `Arity`/`ClassRel`-tagged ones: `HOL.fun_arity` and `HOL.itself_arity`
      // are plain `axiomatization`s, and the shape is what identifies them anyway
      let axiom_props =
        (sess.axioms.iter().flat_map(|(_, x)| x)).filter_map(|e| e.val.0.as_deref()).map(|(p, _)| p);
      // *not* theorem statements: plenty of theorems mention `OFCLASS` without declaring
      // an arity, and a wrong entry here would let a bogus sort obligation through
      for prop in axiom_props {
        let mut constraints: HashMap<&str, Vec<String>> = Default::default();
        let mut t: &Term = &prop.prop;
        while let Term::App(f, arg) = t {
          let Term::App(imp, prem) = &**f else { break };
          let is_imp = match &**imp {
            Term::Const(c, _) | Term::Const2(c, _) => c == "Pure.imp",
            _ => false,
          };
          if !is_imp {
            break
          }
          let Term::OfClass(c, carrier) = &**prem else { break };
          let (Type::Var(x, _, _) | Type::Free(x, _)) = &**carrier else { break };
          constraints.entry(x).or_default().push(c.clone());
          t = arg
        }
        // the carrier of `OFCLASS(T, c)` is `T` written as a term: a type constructor
        // becomes `Const (name, type args)`, a type variable a `Var`
        let Term::OfClass(c, carrier) = t else { continue };
        match &**carrier {
          // `Logic.mk_arity (t, Ss, c) = OFCLASS(t(?'a1::S1, …), c)`
          Type::Type(name, args) => {
            let dom = (args.iter())
              .map(|a| match a {
                Type::Var(x, _, s) | Type::Free(x, s) => {
                  let mut cs = constraints.get(&**x).cloned().unwrap_or_default();
                  cs.extend(s.iter().cloned());
                  cs
                }
                _ => vec![],
              })
              .collect::<Vec<_>>();
            arities.push((name.clone(), dom, c.clone()))
          }
          // `Logic.mk_classrel (c1, c2) = OFCLASS(?'a::c1, c2)`: the sort is on the
          // variable itself here, since a classrel axiom has no premises
          Type::Var(x, _, sort) | Type::Free(x, sort) => {
            let mut cs = constraints.get(&**x).cloned().unwrap_or_default();
            cs.extend(sort.iter().cloned());
            for c1 in cs {
              g.classes.add_classrel(&c1, c)
            }
          }
        }
      }
    }
    let n = arities.len();
    g.classes.close(arities);
    // the declarations every term is checked against: a `Const (c, T)` must have `T` an
    // instance of `c`'s declared type, and a type constructor must be applied to its arity
    for sess in parents.iter().map(|(_, y)| y).chain(std::iter::once(&sess)) {
      for (_, entities) in &sess.consts {
        for e in entities {
          if let Some(v) = e.val.0.as_deref() {
            if v.abbrev.is_none() {
              g.consts.insert(e.name.clone(), (v.args.clone(), v.ty.clone()));
            }
          }
        }
      }
      for (_, entities) in &sess.types {
        for e in entities {
          if let Some(v) = e.val.0.as_deref() {
            g.types.insert(e.name.clone(), v.args.len());
          }
        }
      }
      for (_, entities) in &sess.axioms {
        for e in entities {
          if let Some((prop, _)) = e.val.0.as_deref() {
            g.axiom_props.insert(e.name.clone(), prop.clone());
          }
        }
      }
    }
    if std::env::var_os("SHOW_ALGEBRA").is_some() {
      println!("-- class algebra: {} classes, {n} declared arities ({} from exports), {} completed",
        g.classes.supers.len(), n_exported, g.classes.arities.len());
      for ((t, c), dom) in g.classes.arities.iter().take(8) {
        println!("   arity {t} :: {dom:?} -> {c}");
      }
    }
  }
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
  // for (name, sess) in parents.iter().map(|(x, y)| (*x, y)).chain(std::iter::once((main, &sess))) {
  //   for (theory, entities) in &sess.types {
  //     for entity in entities {
  //       println!("{theory} type: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.consts {
  //     for entity in entities {
  //       println!("{theory} const: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.axioms {
  //     for entity in entities {
  //       println!("{theory} axiom: {}", entity.name);
  //       if let Some(x) = &entity.val.0 {
  //         println!("  = {:?}", x.1)
  //       }
  //     }
  //   }
  //   for (theory, entities) in &sess.thms {
  //     for entity in entities {
  //       println!("{theory} thm: {}", entity.name);
  //       // if let Some(s) = g.proofs.get(&entity.serial) {
  //       //   println!("=> {:#?}", s)
  //       // }
  //       // if let Some(s) = g.traces.get(&entity.serial) {
  //       //   println!("=> {:#?}", s)
  //       // }
  //     }
  //   }
  //   for (theory, entities) in &sess.classes {
  //     for entity in entities {
  //       println!("{theory} class: {}", entity.name);
  //       if let Some(x) = &entity.val.0 {
  //         println!("  = {:?}", x)
  //       } else {
  //         println!("  = none")
  //       }
  //     }
  //   }
  //   for (theory, entities) in &sess.locales {
  //     for entity in entities {
  //       println!("{theory} locale: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.class_rels {
  //     for entity in entities {
  //       println!("{theory} class_rel: {} -> {}", entity.c1, entity.c2)
  //     }
  //   }
  //   for (theory, entities) in &sess.arities {
  //     for entity in entities {
  //       println!("{theory} arity: {}", entity.type_name)
  //     }
  //   }
  //   for (theory, kind, entities) in &sess.other {
  //     for entity in entities {
  //       println!("{theory} {kind}: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.const_defs {
  //     for entity in entities {
  //       println!("{theory} const_def: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.spec_rules {
  //     for entity in entities {
  //       println!("{theory} spec_rule: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.locale_deps {
  //     for entity in entities {
  //       println!("{theory} locale_dep: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.type_defs {
  //     for entity in entities {
  //       println!("{theory} type_def: {}", entity.name)
  //     }
  //   }
  //   for (theory, entities) in &sess.datatypes {
  //     for entity in entities {
  //       println!("{theory} datatype: {}", entity.name)
  //     }
  //   }
  // }
  let mut gthms: HashMap<u32, (usize, usize, usize)> = Default::default();
  for (i, (_, sess)) in parents.iter().enumerate() {
    for (j, (_, thms)) in sess.thms.iter().enumerate() {
      for (k, thm) in thms.iter().enumerate() {
        gthms.insert(thm.serial, (i, j, k));
        g.external.insert(thm.serial);
      }
    }
  }
  // for (&i, p) in &g.proofs {
  //   println!("proofs/{i}: {p:#?}")
  // }
  let mut defs: Vec<(String, Definition)> = vec![];
  let (mut n_unchecked, mut n_bad_defs) = (0usize, 0usize);
  for entity in sess.axioms.iter().flat_map(|(_, x)| x) {
    match entity.val.0.as_deref() {
      None => panic!("axiom {} not exported", entity.name),
      Some((_, AxiomReason::Forgot)) => panic!("axiom missing provenance"),
      Some((prop, AxiomReason::Def { unchecked, overloaded })) => {
        match check_definition(&g, prop) {
          Ok(def) => {
            if *unchecked {
              n_unchecked += 1
            }
            let _ = overloaded;
            defs.push((entity.name.clone(), def))
          }
          Err(msg) => {
            println!("!! definition {}: {msg}", entity.name);
            n_bad_defs += 1
          }
        }
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
      Some((_, AxiomReason::Arity)) => {
        // println!("arity axiom {}: {:?}", entity.name, entity.val.0.as_deref().unwrap().0.prop)
      }
      Some((_, AxiomReason::Typedef)) => {
        // println!("typedef axiom {}: {:?}", entity.name, entity.val.0.as_deref().unwrap().0.prop)
      }
      Some((_, r)) => todo!("reason: {r:?}"),
    }
  }
  {
    // `Defs.define`: a definition may not depend on itself, directly or through others.
    // Overloading makes the node a constant *plus* the head constructors of its type
    // arguments, which is how Isabelle keeps `size :: 'a list ⇒ nat` and
    // `size :: nat ⇒ nat` apart.
    let mut edges: HashMap<DefNode, Vec<DefNode>> = Default::default();
    for (_, d) in &defs {
      edges.entry(d.lhs.clone()).or_default().extend(d.rhs.iter().cloned());
    }
    let mut state: HashMap<DefNode, u8> = Default::default();
    let mut cycles = 0usize;
    let mut stack: Vec<(DefNode, usize)> = vec![];
    for start in edges.keys().cloned().collect::<Vec<_>>() {
      if state.get(&start).is_some() {
        continue
      }
      stack.push((start.clone(), 0));
      state.insert(start, 1);
      while let Some((n, i)) = stack.pop() {
        let next = edges.get(&n).and_then(|v| v.get(i)).cloned();
        match next {
          None => {
            state.insert(n, 2);
          }
          Some(m) => {
            stack.push((n, i + 1));
            match state.get(&m) {
              Some(1) => {
                println!("!! definitional cycle at {m:?}");
                cycles += 1;
              }
              Some(_) => {}
              None => {
                state.insert(m.clone(), 1);
                stack.push((m, 0));
              }
            }
          }
        }
      }
    }
    println!(
      "definitions: {} checked ({n_unchecked} unchecked), {n_bad_defs} malformed, {cycles} cyclic",
      defs.len()
    );
    assert!(n_bad_defs == 0 && cycles == 0, "definition checking failed");
  }
  #[derive(Debug)]
  enum Uses {
    Once,
    Multiple,
    Public,
  }
  enum Elem {
    Start(u32),
    /// the trace is decoded again rather than carried: the stack holds one entry per
    /// theorem whose dependencies are still being checked, and a decoded trace is large
    Finish(u32),
  }
  let mut checked = 0usize;
  // count, and the id of the first theorem that hit it -- enough to reproduce one
  let mut failures: HashMap<(String, String), (usize, u32)> = Default::default();
  let mut reachable: HashSet<u32> = Default::default();
  let mut uses: HashMap<u32, Uses> = Default::default();
  let mut stack: Vec<Elem> = vec![];
  let mut deps_cache: HashMap<u32, Vec<u32>> = Default::default();
  let mut starts = 0usize;
  for i in sess.thms.iter().rev().flat_map(|(_, e)| e.iter().rev()).map(|e| e.serial) {
    if g.traces.contains_key(&i) {
      uses.insert(i, Uses::Public);
      reachable.insert(i);
      stack.push(Elem::Start(i));
    }
  }
  while let Some(elem) = stack.pop() {
    match elem {
      Elem::Start(i) => {
        // A theorem must be checked exactly once, and only once every theorem it cites has
        // been checked -- a citation is verified against what its target was verified to
        // prove.  A dependency reachable from several users must therefore not simply be
        // marked visited (it could then be finished *after* one of them); instead the user
        // is re-scheduled behind its outstanding dependencies.  The dependency list is
        // memoised so that re-scheduling costs no further decoding.
        if g.verified.contains_key(&i) {
          continue
        }
        starts += 1;
        if starts % 200000 == 0 && std::env::var_os("SHOW_MEM").is_some() {
          println!("-- {starts} starts, {} decoded, stack {}", deps_cache.len(), stack.len());
        }
        if starts == 20_000_000 {
          // a cycle in the citation graph would spin here forever: report it
          let mut top: Vec<u32> = vec![];
          for e in stack.iter().rev().take(40) {
            if let Elem::Start(j) = e {
              top.push(*j)
            }
          }
          println!("!! traversal not converging; pending: {top:?}");
          for j in top.iter().take(6) {
            println!("   {j} cites {:?}", deps_cache.get(j));
          }
          std::process::exit(3)
        }
        let deps = match deps_cache.get(&i) {
          Some(deps) => deps,
          None => {
            let blob = g.traces[&i].decode();
            let (bp, root) = BinParser::new(&blob);
            let mut deps = vec![];
            for j in ThmTrace::get_uses(&bp, root) {
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
                reachable.insert(j);
                deps.push(j)
              }
            }
            deps_cache.entry(i).or_insert(deps)
          }
        };
        let todo: Vec<u32> =
          deps.iter().copied().filter(|j| !g.verified.contains_key(j)).collect();
        if todo.is_empty() {
          stack.push(Elem::Finish(i))
        } else {
          stack.push(Elem::Start(i));
          stack.extend(todo.into_iter().rev().map(Elem::Start))
        }
      }
      Elem::Finish(i) => {
        if g.verified.contains_key(&i) {
          continue
        }
        let blob = g.traces[&i].decode();
        let (bp, root) = BinParser::new(&blob);
        // keep going after a failure: one panic per run makes each investigation cost a
        // full pass over the session
        // `ONLY=<serial>` restricts the check to one theorem, for investigating a failure
        // (its dependencies are separate traces, so nothing else is needed)
        // `ONLY=<serial>` restricts checking to one theorem; the others are recorded with
        // what they claim so that citations still resolve and the traversal converges
        if std::env::var("ONLY").is_ok_and(|v| v.parse() != Ok(i)) {
          if let Ok(v) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            Checker::new(&bumpalo::Bump::new(), &g).claim(&bp, root)
          })) {
            g.verified.insert(i, v);
          }
          continue
        }
        if checked % 20000 == 0 && std::env::var_os("SHOW_MEM").is_some() {
          let bytes: usize =
            g.verified.values().map(|v| v.buf.len() + v.strings.iter().map(|s| s.len() + 24).sum::<usize>()).sum();
          let rss = std::fs::read_to_string("/proc/self/statm")
            .ok()
            .and_then(|s| s.split(' ').nth(1).and_then(|x| x.parse::<usize>().ok()))
            .unwrap_or(0) * 4096;
          println!("-- {checked} checked, {} stored, {} MB of statements, RSS {} MB",
            g.verified.len(), bytes >> 20, rss >> 20);
        }
        if std::env::var_os("SHOW_START").is_some() {
          println!("-> checking {i}");
          use std::io::Write;
          std::io::stdout().flush().ok();
        }
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
          Checker::new(&bumpalo::Bump::new(), &g).check(&bp, root)
        }));
        checked += 1;
        // record what this theorem proves, so that citations of it can be checked against
        // it rather than trusted
        match result {
          Ok(v) => {
            g.verified.insert(i, v);
          }
          Err(_) => {
            let (msg, loc) = LAST_PANIC.with(|p| p.borrow().clone());
            let e = failures.entry((loc, msg)).or_insert((0, i));
            e.0 += 1;
            if std::env::var_os("SHOW_FAILS").is_some() {
              println!("   ^^ failure in proof_trace/{i}");
            }
            // record what it *claims* to prove, so that its users are checked against that
            // and the failure is reported once, where it happened
            if let Ok(v) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
              Checker::new(&bumpalo::Bump::new(), &g).claim(&bp, root)
            })) {
              g.verified.insert(i, v);
            }
          }
        }
      }
    }
  }
  if std::env::var_os("DEBUG_RULES").is_some() {
    kernel::RULE_COUNTS.with(|c| {
      let c = c.borrow();
      let mut rows: Vec<_> = c.iter().enumerate().filter(|&(_, &n)| n != 0).collect();
      rows.sort_by_key(|&(_, &n)| std::cmp::Reverse(n));
      for (tag, n) in rows {
        println!("{n:10}  rule {tag}");
      }
    })
  }
  let failed: usize = failures.values().map(|x| x.0).sum();
  println!("\n=== checked {checked} theorems, {failed} failed ===");
  let mut rows: Vec<_> = failures.into_iter().collect();
  rows.sort_by_key(|&(_, (n, _))| std::cmp::Reverse(n));
  for ((loc, msg), (n, first)) in rows {
    println!("{n:6}  {loc}  {msg}  (e.g. proof_trace/{first})");
  }
  Ok(())
}
