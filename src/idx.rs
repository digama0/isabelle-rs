use std::{
  marker::PhantomData,
  ops::{Index, IndexMut, Range},
};

use bit_set::BitSet;

/// A trait for newtyped integers, that can be used as index types in vectors and sets.
pub trait Idx: Copy + Eq + std::hash::Hash + Ord + std::fmt::Debug + Default {
  /// Convert from `T` to `usize`
  fn into_usize(self) -> usize;
  /// Convert from `usize` to `T`
  fn from_usize(_: usize) -> Self;
  /// Generate a fresh variable from a `&mut ID` counter.
  #[must_use]
  fn fresh(&mut self) -> Self {
    let n = *self;
    *self = Self::from_usize(self.into_usize() + 1);
    n
  }
}

impl Idx for usize {
  fn into_usize(self) -> usize {
    self
  }
  fn from_usize(n: usize) -> Self {
    n
  }
}
impl Idx for u32 {
  fn into_usize(self) -> usize {
    self as _
  }
  fn from_usize(n: usize) -> Self {
    n as _
  }
}

/// A vector indexed by a custom indexing type `I`, usually a newtyped integer.
pub struct IdxVec<I, T>(pub Vec<T>, PhantomData<I>);

impl<I, T: std::fmt::Debug> std::fmt::Debug for IdxVec<I, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.0.fmt(f)
  }
}
impl<I, T: dbg_pls::DebugPls> dbg_pls::DebugPls for IdxVec<I, T> {
  fn fmt(&self, f: dbg_pls::Formatter<'_>) {
    self.0.fmt(f)
  }
}

impl<I, T: Clone> Clone for IdxVec<I, T> {
  fn clone(&self) -> Self {
    Self(self.0.clone(), PhantomData)
  }
}

impl<I, T: PartialEq> PartialEq for IdxVec<I, T> {
  fn eq(&self, other: &Self) -> bool {
    self.0 == other.0
  }
}
impl<I, T: Eq> Eq for IdxVec<I, T> {}

impl<I, T> IdxVec<I, T> {
  /// Construct a new empty [`IdxVec`].
  #[must_use]
  pub const fn new() -> Self {
    Self(vec![], PhantomData)
  }

  /// Construct a new [`IdxVec`] with the specified capacity.
  #[must_use]
  pub fn with_capacity(capacity: usize) -> Self {
    Vec::with_capacity(capacity).into()
  }

  /// Construct a new [`IdxVec`] by calling the specified function.
  #[must_use]
  pub fn from_fn(size: usize, f: impl FnMut() -> T) -> Self {
    Self::from(std::iter::repeat_with(f).take(size).collect::<Vec<_>>())
  }

  /// Construct a new [`IdxVec`] using the default element `size` times.
  #[must_use]
  pub fn from_default(size: usize) -> Self
  where
    T: Default,
  {
    Self::from_fn(size, T::default)
  }

  /// The number of elements in the [`IdxVec`].
  #[must_use]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  /// Get a value by index into the vector.
  pub fn get(&self, index: I) -> Option<&T>
  where
    I: Idx,
  {
    self.0.get(I::into_usize(index))
  }

  /// Get a value by index into the vector.
  pub fn get_mut(&mut self, index: I) -> Option<&mut T>
  where
    I: Idx,
  {
    self.0.get_mut(I::into_usize(index))
  }

  /// Returns the value that would be returned by the next call to `push`.
  pub fn peek(&self) -> I
  where
    I: Idx,
  {
    I::from_usize(self.0.len())
  }

  /// Insert a new value at the end of the vector.
  pub fn push(&mut self, val: T) -> I
  where
    I: Idx,
  {
    let id = self.peek();
    self.0.push(val);
    id
  }

  /// Grow the vector until it is long enough that `vec[idx]` will work.
  pub fn extend_to_include(&mut self, idx: I)
  where
    I: Idx,
    T: Default,
  {
    let n = I::into_usize(idx) + 1;
    if self.0.len() < n {
      self.0.resize_with(n, T::default)
    }
  }

  /// Get the element with index `idx`, extending the vector if necessary.
  pub fn get_mut_extending(&mut self, idx: I) -> &mut T
  where
    I: Idx,
    T: Default,
  {
    self.extend_to_include(idx);
    &mut self[idx]
  }

  /// An iterator including the indexes, like `iter().enumerate()`, as `I`.
  pub fn enum_iter(&self) -> impl DoubleEndedIterator<Item = (I, &T)> + Clone
  where
    I: Idx,
  {
    self.0.iter().enumerate().map(|(n, val)| (I::from_usize(n), val))
  }

  /// An iterator including the indexes, like `iter_mut().enumerate()`, as `I`.
  pub fn enum_iter_mut(&mut self) -> impl DoubleEndedIterator<Item = (I, &mut T)>
  where
    I: Idx,
  {
    self.0.iter_mut().enumerate().map(|(n, val)| (I::from_usize(n), val))
  }

  /// Returns `true` if the vector contains no elements.
  #[must_use]
  pub fn is_empty(&self) -> bool {
    self.0.is_empty()
  }
}

impl<I, T> From<Vec<T>> for IdxVec<I, T> {
  fn from(vec: Vec<T>) -> Self {
    Self(vec, PhantomData)
  }
}

impl<I, T> std::iter::FromIterator<T> for IdxVec<I, T> {
  fn from_iter<J: IntoIterator<Item = T>>(iter: J) -> Self {
    Vec::from_iter(iter).into()
  }
}

impl<I, T> Default for IdxVec<I, T> {
  fn default() -> Self {
    vec![].into()
  }
}

impl<I: Idx, T> Index<I> for IdxVec<I, T> {
  type Output = T;
  #[track_caller]
  fn index(&self, index: I) -> &Self::Output {
    &self.0[I::into_usize(index)]
  }
}

impl<I: Idx, T> IndexMut<I> for IdxVec<I, T> {
  #[track_caller]
  fn index_mut(&mut self, index: I) -> &mut Self::Output {
    &mut self.0[I::into_usize(index)]
  }
}

impl<I: Idx, T> Index<Range<I>> for IdxVec<I, T> {
  type Output = [T];
  #[track_caller]
  fn index(&self, r: Range<I>) -> &Self::Output {
    &self.0[I::into_usize(r.start)..I::into_usize(r.end)]
  }
}
impl<'a, I, T: crate::Parse<'a>> crate::Parse<'a> for IdxVec<I, T> {
  fn parse(t: &[crate::Tree<'a>]) -> Self {
    Self(<_>::parse(t), PhantomData)
  }
  fn parse_v2(t: &crate::Tree<'a>) -> Self {
    Self(<_>::parse_v2(t), PhantomData)
  }
}

/// A bit vector indexed by a custom indexing type `I`, usually a newtyped integer.
pub struct IdxBitSet<I>(pub BitSet, PhantomData<I>);

impl<I> std::fmt::Debug for IdxBitSet<I> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.0.fmt(f)
  }
}

impl<I: Idx + dbg_pls::DebugPls> dbg_pls::DebugPls for IdxBitSet<I> {
  fn fmt(&self, f: dbg_pls::Formatter<'_>) {
    f.debug_list().entries(self.iter()).finish()
  }
}

impl<I> Clone for IdxBitSet<I> {
  fn clone(&self) -> Self {
    Self(self.0.clone(), PhantomData)
  }
}

impl<I> std::hash::Hash for IdxBitSet<I> {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.0.hash(state)
  }
}
impl<I> PartialEq for IdxBitSet<I> {
  fn eq(&self, other: &Self) -> bool {
    self.0 == other.0
  }
}
impl<I> Eq for IdxBitSet<I> {}

impl<I> PartialOrd for IdxBitSet<I> {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}
impl<I> Ord for IdxBitSet<I> {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.0.cmp(&other.0)
  }
}

impl<I> IdxBitSet<I> {
  /// Construct a new empty [`IdxBitSet`].
  pub fn new() -> Self {
    Self(BitSet::new(), PhantomData)
  }

  /// Construct a new [`IdxBitSet`] with the specified capacity.
  #[must_use]
  pub fn with_capacity(capacity: usize) -> Self {
    BitSet::with_capacity(capacity).into()
  }

  /// Returns the number of set bits in this set.
  #[must_use]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  /// Returns true if this set contains the specified index.
  pub fn contains(&self, index: I) -> bool
  where
    I: Idx,
  {
    self.0.contains(I::into_usize(index))
  }

  /// Adds a value to the set. Returns `true` if the value was not already
  /// present in the set.
  pub fn insert(&mut self, index: I) -> bool
  where
    I: Idx,
  {
    self.0.insert(I::into_usize(index))
  }

  /// Constructs an [`IdxBitSet`] containing `{index}`, and exactly sized to hold it.
  pub fn single(index: I) -> Self
  where
    I: Idx,
  {
    let n = I::into_usize(index);
    let mut s = BitSet::with_capacity(n + 1);
    s.insert(n);
    Self(s, PhantomData)
  }

  /// Removes a value from the set. Returns `true` if the value was
  /// present in the set.
  pub fn remove(&mut self, index: I) -> bool
  where
    I: Idx,
  {
    self.0.remove(I::into_usize(index))
  }

  /// Intersects in-place with the specified other bit set.
  pub fn intersect_with(&mut self, other: &Self) {
    self.0.intersect_with(&other.0)
  }

  /// Returns true if this set is a subset of the specified other bit set.
  pub fn is_subset(&self, other: &Self) -> bool {
    self.0.is_subset(&other.0)
  }

  /// Unions in-place with the specified other bit set.
  pub fn union_with(&mut self, other: &Self) {
    self.0.union_with(&other.0)
  }

  /// An iterator over the set bits, as `I`.
  pub fn iter(&self) -> impl Iterator<Item = I> + Clone + '_
  where
    I: Idx,
  {
    self.0.iter().map(I::from_usize)
  }

  /// Returns `true` if the set contains no elements.
  #[must_use]
  pub fn is_empty(&self) -> bool {
    self.0.is_empty()
  }
}

impl<I> From<BitSet> for IdxBitSet<I> {
  fn from(set: BitSet) -> Self {
    Self(set, PhantomData)
  }
}

impl<I> Default for IdxBitSet<I> {
  fn default() -> Self {
    Self::new()
  }
}

#[macro_export]
macro_rules! mk_id {
  ($($id:ident($ty:ty),)*) => {
    $(
      #[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
      pub struct $id(pub $ty);
      impl $crate::idx::Idx for $id {
        fn from_usize(n: usize) -> Self { Self(n as $ty) }
        fn into_usize(self) -> usize { self.0 as usize }
      }
      impl std::fmt::Debug for $id {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
          std::fmt::Debug::fmt(&self.0, f)
        }
      }
      impl dbg_pls::DebugPls for $id {
        fn fmt(&self, f: dbg_pls::Formatter<'_>) {
          dbg_pls::DebugPls::fmt(&self.0, f)
        }
      }
      impl std::str::FromStr for $id {
        type Err = std::num::ParseIntError;
        fn from_str(s: &str) -> Result<Self, Self::Err> { <$ty>::from_str(s).map($id) }
      }
      impl<'a> $crate::Parse<'a> for $id {
        fn parse1(t: &$crate::Tree<'a>) -> Self {
          Self(<&str>::parse1(t).parse().unwrap())
        }
        fn parse_v2(t: &$crate::Tree<'a>) -> Self {
          Self(<&str>::parse_v2(t).parse().unwrap())
        }
      }
    )*
  };
}
