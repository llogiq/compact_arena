#![deny(missing_docs)]

//! A crate with a few single-typed arenas that work exclusively with indexes.
//! The indexes are sized with the arena. This can reduce memory footprint when
//! changing pointers to indices e.g. on 64-bit systems.
//!
//! The arenas use "branded indices": The indices contain lifetimes that bind
//! them to the arena so you cannot mix up two arenas by accident. See
//! [Gankro's thesis](https://github.com/Gankro/thesis/blob/master/thesis.pdf)
//! for more information about the concept and it's implementation in Rust.
//!
//! Use the `in_arena` and similar methods to run code within the scope of an
//! arena:
//!
//! # Examples
//!
//! ```rust
//! compact_arena::in_arena(|arena| {
//!     let idx = arena.add(1usize);
//!     assert_eq!(1, arena[idx]);
//! });
//! ```
//!
//! You can use `in_sized_arena` to change the initial size of the backing
//! memory:
//!
//! ```rust
//!# #[allow(dead_code)]
//! compact_arena::in_sized_arena(1, |arena| {
//!     ..
//!# ; arena.add(1usize);
//! });
//! ```
//!
//! You can nest calls to work with multiple arenas:
//!
//! ```rust
//!# #[allow(dead_code)]
//! compact_arena::in_sized_arena(1, |a| {
//!     compact_arena::in_sized_arena(1, |b| {
//!         ..
//!# ; a.add(1u32); b.add(1u32);
//!     })
//! });
//! ```
//!
//! The compiler will give you a scary lifetime error if you mix up arenas:
//!
//! ```rust,compile_fail
//! compact_arena::in_sized_arena(8, |a| {
//!     compact_arena::in_sized_arena(8, |b| {
//!         let i = a.add(1usize);
//!         b[i]
//!     }
//! }
//! ```

use core::ops::{Index, IndexMut};
use core::default::Default;
use core::marker::PhantomData;

#[derive(Copy, Clone, PartialEq, PartialOrd, Eq)]
struct Id<'id>(PhantomData<*mut &'id ()>);

unsafe impl Sync for Id<'_> {}
unsafe impl Send for Id<'_> {}

impl<'id> Default for Id<'id> {
    #[inline]
    fn default() -> Self { Id(PhantomData) }
}

/// An index into the arena
///
/// The only way to get an index into an arena is to `add` a value to it. With
/// an `Idx` you can index or mutably index into the arena to observe or mutate
/// the value.
#[derive(Copy, Clone, PartialOrd, PartialEq, Eq)]
pub struct Idx<'id, I> {
    id: Id<'id>,
    index: I,
}

/// The index type for a small arena is 32 bits large
///
/// # Examples
///
/// ```rust
///# use core::mem::size_of;
///# use compact_arena::Idx32;
/// assert_eq!(size_of::<Idx32<'_>>(), size_of::<u32>());
/// ```
pub type Idx32<'id> = Idx<'id, u32>;

/// A "Small" arena based on a resizable slice (i.e. a `Vec`) that can be
/// indexed with 32-bit `Idx32`s. This can help reduce memory overhead when
/// using many pointer-heavy objects on 64-bit systems.
///
/// You will usually use this type by calling `in_arena` or similar functions.
pub struct SmallArena<'id, T> {
    id: Id<'id>,
    // TODO: Use a custom structure, forbid resizing over 2G items
    data: Vec<T>,
}

const INITIAL_CAPACITY: u32 = 1024 * 1024; // start with 1M elements

/// Run code using an arena. The indirection through a `FnOnce` is required
/// to bind the indices to the arena.
#[inline]
pub fn in_arena<T, F: for<'t> FnOnce(&mut SmallArena<'t, T>) -> O, O>(f: F) -> O {
    in_sized_arena(INITIAL_CAPACITY, f)
}

/// Same as `in_arena`, but allows specifying the initial size of the arena.
#[inline]
pub fn in_sized_arena<T, F, O>(size: u32, f: F) -> O
where F: for<'t> FnOnce(&mut SmallArena<'t, T>) -> O {
    f(&mut SmallArena {
        id: Id::default(),
        data: Vec::with_capacity(size as usize),
    })
}


impl<'id, T> SmallArena<'id, T> {
    /// Add an item to the arena, get an index back
    #[inline]
    pub fn add(&mut self, item: T) -> Idx32<'id> {
        let i = self.data.len() as u32;
        self.data.push(item);
        Idx { id: self.id, index: i }
    }
}

impl<'id, T> Index<Idx32<'id>> for SmallArena<'id, T> {
    type Output = T;

    #[inline]
    fn index(&self, i: Idx32<'id>) -> &T {
        unsafe { &self.data.get_unchecked(i.index as usize) }
    }
}

impl<'id, T> IndexMut<Idx32<'id>> for SmallArena<'id, T> {
    #[inline]
    fn index_mut(&mut self, i: Idx32<'id>) -> &mut T {
        unsafe { self.data.get_unchecked_mut(i.index as usize) }
    }
}

const TINY_ARENA_ITEMS: usize = 65535;
const NANO_ARENA_ITEMS: usize = 255;

/// The index type for a tiny arena is 16 bits large
///
/// # Examples:
///
/// ```rust
///# use compact_arena::Idx16;
///# use core::mem::size_of;
/// assert_eq!(size_of::<Idx16<'_>>(), size_of::<u16>());
/// ```
pub type Idx16<'id> = Idx<'id, u16>;

/// The index type for a nano arena is 8 bits large
///
/// # Examples:
///
/// ```rust
///# use compact_arena::Idx8;
///# use core::mem::size_of;
/// assert_eq!(size_of::<Idx8<'_>>(), size_of::<u8>());
/// ```
pub type Idx8<'id> = Idx<'id, u8>;

pub use tiny_arena::{in_tiny_arena, TinyArena, in_nano_arena, NanoArena};

#[cfg(not(feature = "uninit"))]
mod tiny_arena {
    use crate::{Id, Idx16, Idx8, TINY_ARENA_ITEMS, NANO_ARENA_ITEMS};
    use core::ops::{Index, IndexMut};

    /// Run code using a tiny arena. The indirection through a `FnOnce` is
    /// required to bind the indices to the arena. This version only works
    /// for types that implement `Default` and `Copy`. You can use the `uninit`
    /// feature to remove that restriction, at the cost of some unsafe code.
    ///
    /// # Examples
    ///
    /// ```rust
    /// compact_arena::in_tiny_arena(|arena| {
    ///     let idx = arena.add(1usize);
    ///     assert_eq!(1, arena[idx]);
    /// });
    /// ```
    #[inline]
    pub fn in_tiny_arena<F, O, T: Default + Copy>(f: F) -> O
    where F: for<'t> FnOnce(&mut TinyArena<'t, T>) -> O {
        f(&mut TinyArena {
            id: Id::default(),
            data: [Default::default(); TINY_ARENA_ITEMS],
            len: 0,
        })
    }

    /// A "tiny" arena containing <64K elements. This variant only works with
    /// types implementing `Default`.
    ///
    /// You will likely use this via the `in_tiny_arena` function.
    pub struct TinyArena<'id, T> {
        id: Id<'id>,
        len: u16,
        data: [T; TINY_ARENA_ITEMS],
    }

    impl<'id, T> TinyArena<'id, T> {
        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx16<'id> {
            let i = self.len;
            assert!((i as usize) < TINY_ARENA_ITEMS);
            self.data[i as usize] = item;
            self.len += 1;
            Idx16 { id: self.id, index: i }
        }
    }

    impl<'id, T> Index<Idx16<'id>> for TinyArena<'id, T> {
        type Output = T;
        fn index(&self, i: Idx16<'id>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<'id, T> IndexMut<Idx16<'id>> for TinyArena<'id, T> {
        fn index_mut(&mut self, i: Idx16<'id>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }

    /// Run code using a nano arena. The indirection through a `FnOnce` is
    /// required to bind the indices to the arena. This version only works
    /// for types that implement `Default` and `Copy`. You can use the `uninit`
    /// feature to remove that restriction, at the cost of some unsafe code.
    ///
    /// # Examples
    ///
    /// ```rust
    /// compact_arena::in_nano_arena(|arena| {
    ///     let idx = arena.add(1usize);
    ///     assert_eq!(1, arena[idx]);
    /// });
    /// ```
    #[inline]
    pub fn in_nano_arena<F, O, T: Default + Copy>(f: F) -> O
    where F: for<'t> FnOnce(&mut NanoArena<'t, T>) -> O {
        f(&mut NanoArena {
            id: Id::default(),
            data: [Default::default(); NANO_ARENA_ITEMS],
            len: 0,
        })
    }

    /// A "nano" arena containing 255 elements. This variant only works with
    /// types implementing `Default`.
    ///
    /// You will likely use this via the `in_nano_arena` function.
    pub struct NanoArena<'id, T> {
        id: Id<'id>,
        len: u8,
        data: [T; NANO_ARENA_ITEMS],
    }

    impl<'id, T> NanoArena<'id, T> {
        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx8<'id> {
            let i = self.len;
            assert!((i as usize) < NANO_ARENA_ITEMS);
            self.data[i as usize] = item;
            self.len += 1;
            Idx8 { id: self.id, index: i }
        }
    }

    impl<'id, T> Index<Idx8<'id>> for NanoArena<'id, T> {
        type Output = T;
        fn index(&self, i: Idx8<'id>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<'id, T> IndexMut<Idx8<'id>> for NanoArena<'id, T> {
        fn index_mut(&mut self, i: Idx8<'id>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }
}

#[cfg(feature = "uninit")]
mod tiny_arena {
    use crate::{Id, Idx16, Idx8, TINY_ARENA_ITEMS, NANO_ARENA_ITEMS};
    use core::mem::{self, ManuallyDrop};
    use core::ops::{Index, IndexMut};

    /// Run code using a "tiny" arena. The indirection through a `FnOnce` is
    /// required to bind the indices to the arena.
    ///
    /// # Examples
    ///
    /// ```rust
    /// compact_arena::in_tiny_arena(|arena| {
    ///     let idx = arena.add(1usize);
    ///     assert_eq!(1, arena[idx]);
    /// });
    /// ```
    #[inline]
    pub fn in_tiny_arena<T, F: for<'t> FnOnce(&mut TinyArena<'t, T>) -> O, O>(f: F) -> O {
        assert!(mem::size_of::<T>() > 0, "zero-sized types are not allowed");
        f(&mut TinyArena {
            id: Id::default(),
            data: unsafe { mem::uninitialized() },
            len: 0,
        })
    }

    /// A "tiny" arena containing <64K elements.
    pub struct TinyArena<'id, T> {
        id: Id<'id>,
        len: u16,
        data: [ManuallyDrop<T>; TINY_ARENA_ITEMS],
    }

    impl<'id, T> TinyArena<'id, T> {
        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx16<'id> {
            let i = self.len;
            self.data[i as usize] = ManuallyDrop::new(item);
            self.len += 1;
            Idx16 { id: self.id, index: i }
        }

        /// dropping the arena drops all values
        pub fn drop(&mut self) {
            for i in 0..self.len as usize {
                unsafe { ManuallyDrop::drop(&mut self.data[i]) };
            }
            self.len = 0;
        }
    }

    impl<'id, T> Index<Idx16<'id>> for TinyArena<'id, T> {
        type Output = T;
        fn index(&self, i: Idx16<'id>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<'id, T> IndexMut<Idx16<'id>> for TinyArena<'id, T> {
        fn index_mut(&mut self, i: Idx16<'id>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }

    // nano arena

    /// Run code using a "nano" arena. The indirection through a `FnOnce` is
    /// required to bind the indices to the arena.
    ///
    /// # Examples
    ///
    /// ```rust
    /// compact_arena::in_tiny_arena(|arena| {
    ///     let idx = arena.add(1usize);
    ///     assert_eq!(1, arena[idx]);
    /// });
    /// ```
    #[inline]
    pub fn in_nano_arena<T, F: for<'t> FnOnce(&mut NanoArena<'t, T>) -> O, O>(f: F) -> O {
        assert!(mem::size_of::<T>() > 0, "zero-sized types are not allowed");
        f(&mut NanoArena {
            id: Id::default(),
            data: unsafe { mem::uninitialized() },
            len: 0,
        })
    }

    /// A "nano" arena containing up to 255 elements.
    pub struct NanoArena<'id, T> {
        id: Id<'id>,
        len: u8,
        data: [ManuallyDrop<T>; NANO_ARENA_ITEMS],
    }

    impl<'id, T> NanoArena<'id, T> {
        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx8<'id> {
            let i = self.len;
            self.data[i as usize] = ManuallyDrop::new(item);
            self.len += 1;
            Idx8 { id: self.id, index: i }
        }

        /// dropping the arena drops all values
        pub fn drop(&mut self) {
            for i in 0..self.len as usize {
                unsafe { ManuallyDrop::drop(&mut self.data[i]) };
            }
            self.len = 0;
        }
    }

    impl<'id, T> Index<Idx8<'id>> for NanoArena<'id, T> {
        type Output = T;
        fn index(&self, i: Idx8<'id>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<'id, T> IndexMut<Idx8<'id>> for NanoArena<'id, T> {
        fn index_mut(&mut self, i: Idx8<'id>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }
}
