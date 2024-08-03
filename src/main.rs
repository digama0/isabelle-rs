use itertools::Itertools;
use rusqlite::{Connection, Result};
use std::{collections::HashMap, io::Read, path::Path};

extern crate self as isabelle_rs;

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
}
impl<'a> Parse<'a> for &'a str {
  fn parse1(t: &Tree<'a>) -> Self {
    let Tree::Text(a) = *t else { panic!() };
    std::str::from_utf8(a).unwrap()
  }
}
impl<'a> Parse<'a> for String {
  fn parse1(t: &Tree<'a>) -> Self {
    <&str>::parse1(t).to_owned()
  }
}
impl<'a> Parse<'a> for usize {
  fn parse1(t: &Tree<'a>) -> Self {
    <&str>::parse1(t).parse().unwrap()
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
}
impl<'a> Parse<'a> for () {
  fn parse1(t: &Tree<'a>) -> Self {
    match <&str>::parse1(t) {
      "" => (),
      _ => panic!(),
    }
  }
  fn parse(t: &[Tree<'a>]) -> Self {
    assert!(t.is_empty())
  }
}
impl<'a, A: Parse<'a>, B: Parse<'a>> Parse<'a> for (A, B) {
  fn parse(t: &[Tree<'a>]) -> Self {
    let [a, b] = t else { panic!() };
    (A::parse1_node(a), B::parse1_node(b))
  }
}
impl<'a, A: Parse<'a>, B: Parse<'a>, C: Parse<'a>> Parse<'a> for (A, B, C) {
  fn parse(t: &[Tree<'a>]) -> Self {
    let [a, b, c] = t else { panic!() };
    (A::parse1_node(a), B::parse1_node(b), C::parse1_node(c))
  }
}
impl<'a, T: Parse<'a>> Parse<'a> for Vec<T> {
  fn parse(t: &[Tree<'a>]) -> Self {
    t.iter().map(|a| T::parse1_node(a)).collect()
  }
}
impl<'a, T: Parse<'a>> Parse<'a> for Box<T> {
  fn parse(t: &[Tree<'a>]) -> Self {
    Box::new(T::parse(t))
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

enum Type {
  #[allow(clippy::enum_variant_names)]
  Type(String, Vec<Type>),
  Free(String, Sort),
  // Var(String, usize, Sort),
}

impl std::fmt::Debug for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Type(t, ts) => {
        if "fun" == t {
          write!(f, "({:?} -> {:?})", ts[0], ts[1])?;
        } else {
          write!(f, "{t}")?;
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
      } // Self::Var(c, i, ts) => {
        //   write!(f, "v.{c}.{i}")?;
        //   if !ts.is_empty() {
        //     write!(f, "[{:?}]", ts.iter().format(", "))?;
        //   }
        //   Ok(())
        // }
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
  Free(String, Option<Box<Type>>),
  // Var(String, usize, Option<Box<Type>>),
  Bound(usize),
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
        write!(f, "{c}")?;
        if !cs.is_empty() {
          write!(f, "({:?})", cs.iter().format(", "))?;
        }
        Ok(())
      }
      Term::Free(v, None) => write!(f, "{v}"),
      Term::Free(v, Some(ty)) => write!(f, "{v}:{ty:?}"),
      // Term::Var(v, i, None) => write!(f, "v.{v}.{i}"),
      // Term::Var(v, i, Some(ty)) => write!(f, "v.{v}.{i}:{ty:?}"),
      &Term::Bound(i) => write!(f, "{}", ctx[ctx.len() - i - 1]),
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
        write!(f, "OfClass({c}, ")?;
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
        assert!(thm_name == (String::new(), 0));
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
  fn as_node(&self) -> &[Tree<'a>] {
    match self {
      Tree::Node(ts) => ts,
      Tree::Properties(attrs) if attrs.is_empty() => &[],
      _ => panic!(),
    }
  }
}

#[derive(Default)]
struct Properties {
  name: String,
  xname: String,
  pos: (usize, usize),
  label: String,
  file: String,
  id: usize,
  serial: usize,
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
  pos: (usize, usize),
  label: String,
  file: String,
  id: usize,
  serial: usize,
  val: T,
}
impl<'a, T: Parse<'a>> Parse<'a> for Entity<T> {
  fn parse1_node(this: &Tree<'a>) -> Self {
    let Tree::Elem(b"entity", props, ts) = this else { panic!() };
    let Properties { name, xname, pos, label, file, id, serial } = Properties::from_attrs(props);
    Entity { name, xname, pos, label, file, id, serial, val: T::parse(ts) }
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

type AxiomEntry = Prop;

#[derive(Debug)]
struct ThmData {
  proof: ProofBox,
  deps: Vec<(String, usize)>,
}
impl<'a> Parse<'a> for ThmData {
  fn parse(t: &[Tree<'a>]) -> Self {
    let (prop, deps, proof) = <_>::parse(t);
    Self { proof: ProofBox { prop, proof }, deps }
  }
}
type ThmEntry = OptBox<ThmData>;

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
  pos: (usize, usize),
  label: String,
  file: String,
  id: usize,
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
  axioms: Vec<AxiomEntry>,
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
  pos: (usize, usize),
  label: String,
  file: String,
  id: usize,
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

fn main() -> Result<()> {
  let sess = std::env::args().nth(1).unwrap();
  let path = format!("/home/mario/.isabelle/heaps/polyml-5.9.1_x86_64_32-linux/log/{sess}.db");
  let file = Path::new(&path);
  assert!(file.exists());
  let mut proofs: HashMap<usize, ProofBox> = Default::default();
  let mut types: Vec<(String, Entities<TypeEntry>)> = vec![];
  let mut consts: Vec<(String, Entities<ConstEntry>)> = vec![];
  let mut axioms: Vec<(String, Entities<AxiomEntry>)> = vec![];
  let mut thms: Vec<(String, Entities<ThmEntry>)> = vec![];
  let mut classes: Vec<(String, Entities<ClassEntry>)> = vec![];
  let mut locales: Vec<(String, Entities<LocaleEntry>)> = vec![];
  let mut other: Vec<(String, String, Entities<()>)> = vec![];
  let mut const_defs: Vec<(String, Vec<ConstDef>)> = vec![];
  let mut spec_rules: Vec<(String, Vec<SpecRule>)> = vec![];
  let mut class_rels: Vec<(String, Vec<ClassRelEntry>)> = vec![];
  let mut arities: Vec<(String, Vec<Arity>)> = vec![];
  let mut locale_deps: Vec<(String, Entities<LocaleDepEntry>)> = vec![];
  let mut type_defs: Vec<(String, Vec<TypeDef>)> = vec![];
  let mut datatypes: Vec<(String, Vec<Datatype>)> = vec![];
  {
    let db = Connection::open(file)?;
    let mut q = db.prepare("select * from isabelle_exports")?;
    let mut rows = q.query(())?;
    while let Some(row) = rows.next()? {
      #[derive(Debug)]
      enum RowType<'a> {
        Proof(usize),
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
          RowType::Proof(s.parse().unwrap())
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
              _ => continue,
            }
          }
        }
      };
      assert!(row.get(4)?);
      let reader = std::io::Cursor::new(row.get_ref(5)?.as_blob()?);
      let mut out = vec![];
      zstd::stream::Decoder::new(reader).unwrap().read_to_end(&mut out).unwrap();
      let parse = parse(&out);
      match name {
        RowType::Proof(i) => {
          proofs.insert(i, ProofBox::parse(&parse));
        }
        RowType::Types(theory) => types.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Consts(theory) => consts.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Axioms(theory) => axioms.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Thms(theory) => thms.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::ConstDefs(theory) => const_defs.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::SpecRules(theory) => spec_rules.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Classes(theory) => classes.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::ClassRels(theory) => class_rels.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Arities(theory) => arities.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Locales(theory) => locales.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::LocaleDeps(theory) => locale_deps.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::TypeDefs(theory) => type_defs.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Datatypes(theory) => datatypes.push((theory.to_owned(), <_>::parse(&parse))),
        RowType::Other(theory, kind) => {
          other.push((theory.to_owned(), kind.to_owned(), <_>::parse(&parse)))
        }
      }
    }
  }
  for (theory, entities) in &types {
    for entity in entities {
      println!("{theory} type: {entity:#?}")
    }
  }
  for (theory, entities) in &consts {
    for entity in entities {
      println!("{theory} const: {entity:#?}")
    }
  }
  for (theory, entities) in &axioms {
    for entity in entities {
      println!("{theory} axiom: {entity:#?}")
    }
  }
  for (theory, entities) in &thms {
    for entity in entities {
      println!("{theory} thm: {entity:#?}\n=> {:#?}", proofs[&entity.serial])
    }
  }
  for (theory, entities) in &classes {
    for entity in entities {
      println!("{theory} class: {entity:#?}")
    }
  }
  for (theory, entities) in &locales {
    for entity in entities {
      println!("{theory} locale: {entity:#?}")
    }
  }
  for (theory, entities) in &class_rels {
    for entity in entities {
      println!("{theory} class_rel: {entity:#?}")
    }
  }
  for (theory, entities) in &arities {
    for entity in entities {
      println!("{theory} arity: {entity:#?}")
    }
  }
  for (theory, kind, entities) in &other {
    for entity in entities {
      println!("{theory} {kind}: {entity:#?}")
    }
  }
  for (theory, entities) in &const_defs {
    for entity in entities {
      println!("{theory} const_def: {entity:#?}")
    }
  }
  for (theory, entities) in &spec_rules {
    for entity in entities {
      println!("{theory} spec_rule: {entity:#?}")
    }
  }
  for (theory, entities) in &locale_deps {
    for entity in entities {
      println!("{theory} locale_dep: {entity:#?}")
    }
  }
  for (theory, entities) in &type_defs {
    for entity in entities {
      println!("{theory} type_def: {entity:#?}")
    }
  }
  for (theory, entities) in &datatypes {
    for entity in entities {
      println!("{theory} datatype: {entity:#?}")
    }
  }
  // for (i, p) in proofs.iter().enumerate() {
  //   println!("proofs/{i}: {p:#?}")
  // }
  Ok(())
}
