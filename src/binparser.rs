use dbg_pls::DebugPls;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug, DebugPls)]
enum ObjType {
  Regular = 0,
  Byte = 1,
  Code = 2,
  Closure = 3,
}

#[derive(Clone, Copy, Debug, DebugPls)]
struct Metadata(u32);
impl Metadata {
  fn obj_type(self) -> ObjType {
    match (self.0 >> 24) & 3 {
      0 => ObjType::Regular,
      1 => ObjType::Byte,
      2 => ObjType::Code,
      3 => ObjType::Closure,
      _ => unreachable!(),
    }
  }
  fn len(self) -> u32 {
    self.0 & 0xFFFFFF
  }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, DebugPls, PartialEq, Eq, Hash)]
pub struct TagPtr(u32);
impl TagPtr {
  pub const ZERO: Self = TagPtr(1);
  fn unpack(self) -> Obj {
    if self.0 & 1 != 0 {
      Obj::UInt(self.0 >> 1)
    } else {
      Obj::Ptr(Ptr((self.0 >> 1).checked_sub(1).expect("null pointer")))
    }
  }
  pub fn as_ptr(self) -> Ptr {
    match self.unpack() {
      Obj::Ptr(p) => p,
      _ => panic!("expected pointer"),
    }
  }
  pub fn as_uint(self) -> u32 {
    match self.unpack() {
      Obj::UInt(n) => n,
      _ => panic!("expected pointer"),
    }
  }
}
impl PartialOrd for TagPtr {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}
impl Ord for TagPtr {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.unpack().cmp(&other.unpack())
  }
}

#[derive(Clone, Copy, Debug, DebugPls, PartialOrd, Ord, PartialEq, Eq)]
pub struct Ptr(u32);

#[derive(Clone, Copy, Debug, DebugPls, PartialOrd, Ord, PartialEq, Eq)]
pub enum Obj {
  UInt(u32),
  Ptr(Ptr),
}

#[derive(Clone, Copy, Debug, DebugPls)]
pub enum Value<'a> {
  Byte(&'a [u8]),
  Tuple(&'a [TagPtr]),
}

impl<'a> Value<'a> {
  pub fn as_bytes(self) -> &'a [u8] {
    match self {
      Value::Byte(s) => s,
      _ => panic!("expected pointer"),
    }
  }
  pub fn as_tuple(self) -> &'a [TagPtr] {
    match self {
      Value::Tuple(p) => p,
      _ => panic!("expected pointer"),
    }
  }
  pub fn as_tuple_n<const N: usize>(self) -> &'a [TagPtr; N] {
    self.as_tuple().try_into().expect("incorrect length")
  }

  pub fn as_str(self) -> &'a [u8] {
    let (len, rest) = self.as_bytes().split_at(4);
    let len = u32::from_le_bytes(len.try_into().unwrap());
    &rest[..len as usize]
  }
}

#[derive(Debug, DebugPls)]
pub struct BinParser<'a> {
  mem: &'a [u32],
  ptrs: Vec<u32>,
}

impl<'a> BinParser<'a> {
  pub fn new(mem: &'a [u32]) -> (Self, TagPtr) {
    let (&root, mem) = mem.split_last().unwrap();
    let mut ptrs = vec![];
    let mut p = 0;
    // println!("{mem:08x?}");
    while let Some(meta) = mem.get(p as usize).copied().map(Metadata) {
      // println!(
      //   "{} = {:?}: {:x?}",
      //   ptrs.len(),
      //   meta.obj_type(),
      //   &mem[p as usize + 1..][..meta.len() as usize]
      // );
      ptrs.push(p);
      p += meta.len() + 1;
    }
    // println!("{p:?}");
    // println!("{ptrs:?}");
    // println!("{:?}", TagPtr(root).unpack());
    assert!(p as usize == mem.len());
    (Self { mem, ptrs }, TagPtr(root))
  }

  pub fn get(&self, p: Ptr) -> Value<'a> {
    let i = self.ptrs[p.0 as usize] as usize;
    let meta = Metadata(self.mem[i]);
    let data = &self.mem[i + 1..][..meta.len() as usize];
    match meta.obj_type() {
      ObjType::Regular => Value::Tuple(unsafe { data.align_to().1 }),
      ObjType::Byte => Value::Byte(unsafe { data.align_to().1 }),
      ObjType::Code | ObjType::Closure => panic!(),
    }
  }

  pub fn get_enum(&self, p: TagPtr) -> (u32, &'a [TagPtr]) {
    match p.unpack() {
      Obj::UInt(tag) => (tag, &[]),
      Obj::Ptr(p) => {
        let (tag, rest) = self.get(p).as_tuple().split_first().expect("missing tag");
        (tag.as_uint(), rest)
      }
    }
  }

  pub fn to_tree(&self, p: TagPtr) -> Tree<'a> {
    match p.unpack() {
      Obj::UInt(n) => Tree::UInt(n),
      Obj::Ptr(p) => match self.get(p) {
        Value::Byte(bs) => Tree::Bytes(bs),
        Value::Tuple(ps) => Tree::Tuple(ps.iter().map(|&p| self.to_tree(p)).collect()),
      },
    }
  }

  pub fn parse<C, T: BinParse<'a, C>>(&self, ctx: &mut C, p: TagPtr) -> T {
    T::parse(ctx, self, p)
  }

  pub fn parse_list(&self, mut p: TagPtr) -> ParseList<'_> {
    ParseList(self, p)
  }
}

#[derive(Clone)]
pub struct ParseList<'a>(&'a BinParser<'a>, TagPtr);
impl Iterator for ParseList<'_> {
  type Item = TagPtr;
  fn next(&mut self) -> Option<Self::Item> {
    match self.1.unpack() {
      Obj::UInt(0) => None,
      Obj::Ptr(ptr) => {
        let &[a, b] = self.0.get(ptr).as_tuple_n();
        self.1 = b;
        Some(a)
      }
      _ => panic!(),
    }
  }
  fn size_hint(&self) -> (usize, Option<usize>) {
    let n = self.len();
    (n, Some(n))
  }
}
impl ExactSizeIterator for ParseList<'_> {
  fn len(&self) -> usize {
    self.clone().count()
  }
}

#[derive(Debug, DebugPls)]
pub enum Tree<'a> {
  UInt(u32),
  Bytes(&'a [u8]),
  Tuple(Box<[Tree<'a>]>),
}

pub trait BinParse<'a, C>: Sized {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, p: TagPtr) -> Self;
}
impl<'a, C> BinParse<'a, C> for TagPtr {
  fn parse(_: &mut C, _: &BinParser<'a>, p: TagPtr) -> Self {
    p
  }
}
impl<'a, C, T: BinParse<'a, C>, const N: usize> BinParse<'a, C> for [T; N] {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, p: TagPtr) -> Self {
    bp.get(p.as_ptr()).as_tuple_n().map(|p| bp.parse(ctx, p))
  }
}

impl<'a, C, T: BinParse<'a, C>> BinParse<'a, C> for Vec<T> {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, mut p: TagPtr) -> Self {
    bp.parse_list(p).map(|a| bp.parse(ctx, a)).collect()
  }
}
impl<'a, C, T: BinParse<'a, C>> BinParse<'a, C> for Box<[T]> {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, mut p: TagPtr) -> Self {
    <Vec<T>>::parse(ctx, bp, p).into_boxed_slice()
  }
}
impl<'a, C, T: BinParse<'a, C>> BinParse<'a, C> for Box<T> {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, mut p: TagPtr) -> Self {
    Box::new(T::parse(ctx, bp, p))
  }
}

impl<'a, C, T: BinParse<'a, C>> BinParse<'a, C> for Option<T> {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, mut p: TagPtr) -> Self {
    match p.unpack() {
      Obj::UInt(0) => None,
      Obj::Ptr(ptr) => {
        let &[a] = bp.get(ptr).as_tuple_n();
        Some(bp.parse(ctx, a))
      }
      _ => panic!(),
    }
  }
}

impl<'a, C, A: BinParse<'a, C>, B: BinParse<'a, C>> BinParse<'a, C> for (A, B) {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, p: TagPtr) -> Self {
    let &[a, b] = bp.get(p.as_ptr()).as_tuple_n();
    (bp.parse(ctx, a), bp.parse(ctx, b))
  }
}

impl<'a, Cx, A: BinParse<'a, Cx>, B: BinParse<'a, Cx>, C: BinParse<'a, Cx>> BinParse<'a, Cx>
  for (A, B, C)
{
  fn parse(ctx: &mut Cx, bp: &BinParser<'a>, p: TagPtr) -> Self {
    let &[a, b, c] = bp.get(p.as_ptr()).as_tuple_n();
    (bp.parse(ctx, a), bp.parse(ctx, b), bp.parse(ctx, c))
  }
}

impl<'a, C> BinParse<'a, C> for u32 {
  fn parse(_: &mut C, _: &BinParser<'a>, p: TagPtr) -> Self {
    p.as_uint()
  }
}

impl<'a, C> BinParse<'a, C> for crate::kernel::HypId {
  fn parse(ctx: &mut C, bp: &BinParser<'a>, p: TagPtr) -> Self {
    Self(p.as_uint())
  }
}
