#![deny(missing_docs)]
#![deny(warnings)]

//! A crate with a few single-typed arenas that work exclusively with indexes.
//! The indexes are sized with the arena. This can reduce memory footprint when
//! changing pointers to indices e.g. on 64-bit systems.
//!
//! The arenas use a variant of "branded indices": The indices contain a type
//! tag that binds them to their respective arena so you cannot mix up two
//! arenas by accident. Unlike the [indexing](https://crates.io/crates/indexing)
//! crate, this implements the type tags as actual unique types. This has the
//! downside of not being able to `Sync` or `Send` arenas or indices, but on the
//! other hand, we can store indices within objects that we put into the arena,
//! which is a boon to things like graph data structures.
//!
//! A word of warning: The soundness of this isn't proven, and it may well be
//! possible to use the macros provided in this crate to create undefined
//! behavior. For simple use cases, you should be pretty safe.
//!
//! Use the `mk_arena!` to create an arena, then `add` items to it and index it
//! with `arena[idx]`.
//!
//! # Examples
//!
//! ```
//!# use compact_arena::mk_arena;
//! mk_arena!(arena);
//! let idx = arena.add(1usize);
//! assert_eq!(1, arena[idx]);
//! ```
//!
//! You can give `mk_arena!` a second argument to change the initial capacity
//! of the backing memory:
//!
//! ```
//!# #[allow(dead_code)]
//!# use compact_arena::mk_arena;
//! mk_arena!(arena, 1);
//! ..
//!# ; arena.add(1usize);
//! ```
//!
//! You can work with multiple arenas:
//!
//! ```
//!# #[allow(dead_code)]
//!# use compact_arena::mk_arena;
//! mk_arena!(a, 1);
//! mk_arena!(b, 1);
//! ..
//!# ; a.add(1u32); b.add(1u32);
//! ```
//!
//! The compiler gives you a type error if you mix up arenas:
//!
//! ```compile_fail
//!# use compact_arena::mk_arena;
//! mk_arena!(a, 1);
//! mk_arena!(b, 1);
//! let i = a.add(1usize);
//! let _ = b[i];
//! ```
//!
//! The indices should not be able to escape the block with the `mk_arena` call
//!
//! ```compile_fail
//!# use compact_arena::mk_arena;
//! let idx = { mk_arena!(arena, 1); arena.add(1usize)) };
//! assert!(core::mem::size_of_val(&a) == 4);
//! ```
//!
//! Also, arenas may not be instantiated recursively:
//!
//! ```compile_fail
//!# use compact_arena::{mk_arena, Idx32};
//! fn recursive(idx: Option<Box<dyn std::any::Any>>) {
//!     mk_arena!(arena, 2); // `tag` does not live long enough
//!     if let Some(idx) = idx {
//!         assert_eq!("hello", arena[*idx.downcast().unwrap()]);
//!     } else {
//!         recursive(Some(Box::new(arena.add("hello"))));
//!     }
//! }
//! recursive(None);
//! ```

use core::fmt::{Debug, Display, Formatter, Result as FmtResult};
use core::ops::{Index, IndexMut};
use core::marker::PhantomData;
use core::result::Result;
use std::error::Error;

#[derive(Copy, Clone, PartialOrd, PartialEq, Eq)]
struct InvariantLifetime<'a>(PhantomData<fn(&'a ()) -> &'a ()>);

/// An index into the arena. You will not directly use this type, but one of
/// the aliases this crate provides (`Idx32`, `Idx16` or `Idx8`).
///
/// The only way to get an index into an arena is to `add` a value to it. With
/// an `Idx` you can index or mutably index into the arena to observe or mutate
/// the value.
#[derive(Copy, Clone, PartialOrd, PartialEq, Eq)]
pub struct Idx<'tag, I: Copy + Clone> {
    index: I,
    tag: InvariantLifetime<'tag>,
}

/// The index type for a small arena is 32 bits large. You will usually get the
/// index from the arena and use it by indexing, e.g. `arena[index]`.
///
/// # Examples
///
/// ```
///# use {compact_arena::Idx32, core::mem::size_of};
/// assert_eq!(size_of::<Idx32<'_>>(), size_of::<u32>());
/// ```
pub type Idx32<'tag> = Idx<'tag, u32>;

/// The index type for a tiny arena is 16 bits large. You will usually get the
/// index from the arena and use it by indexing, e.g. `arena[index]`.
///
/// # Examples:
///
/// ```
///# use {compact_arena::Idx16, core::mem::size_of};
/// assert_eq!(size_of::<Idx16<'_>>(), size_of::<u16>());
/// ```
pub type Idx16<'tag> = Idx<'tag, u16>;

/// The index type for a nano arena is 8 bits large. You will usually get the
/// index from the arena and use it by indexing, e.g. `arena[index]`.
///
/// # Examples:
///
/// ```
///# use {compact_arena::Idx8, core::mem::size_of};
/// assert_eq!(size_of::<Idx8<'_>>(), size_of::<u8>());
/// ```
pub type Idx8<'tag> = Idx<'tag, u8>;

/// An error type that gets returned on trying to add an element to an already
/// full arena. It contains the element so you can reuse it
pub struct CapacityExceeded<T>(T);

impl<T> CapacityExceeded<T> {
    /// Consumes self and returns the contained value.
    pub fn into_value(self) -> T { self.0 }
}

impl<T> Debug for CapacityExceeded<T> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "Capacity Exceeded")
    }
}

impl<T> Display for CapacityExceeded<T> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "Capacity Exceeded")
    }
}

impl<T> Error for CapacityExceeded<T> {
    fn description(&self) -> &str { "Capacity exceeded" }
}

/// A "Small" arena based on a resizable slice (i.e. a `Vec`) that can be
/// indexed with 32-bit `Idx32`s. This can help reduce memory overhead when
/// using many pointer-heavy objects on 64-bit systems.
///
/// You can obtain an instance of this type by calling `mk_arena`.
pub struct SmallArena<'tag, T> {
    tag: InvariantLifetime<'tag>,
    // TODO: Use a custom structure, forbid resizing over 2G items
    data: Vec<T>,
}

/// Run code using an arena. The indirection through the macro is required
/// to safely bind the indices to the arena. The macro takes an identifier that
/// will be bound to the `&mut Arena<_, _>` and an expression that will be
/// executed within a block where the arena is instantiated. The arena will be
/// dropped afterwards.
///
/// # Examples
///
/// ```
///# use compact_arena::mk_arena;
/// mk_arena!(arena);
/// let half = arena.add(21);
/// assert_eq!(42, arena[half] + arena[half]);
/// ```
///
/// You can also specify an initial capacity after the arena identifier:
///
/// ```
///# #[allow(dead_code)]
///# use compact_arena::mk_arena;
/// mk_arena!(arena, 65536);
///# arena.add(2usize);
/// ..
///# ;
/// ```
///
/// The capacity will be extended automatically, so `new_arena!(0)` creates a
/// valid arena with initially zero capacity that will be extended on the first
/// `add`.
#[macro_export]
macro_rules! mk_arena {
    ($name:ident) => { mk_arena!($name, 1024*1024) };
    ($name:ident, $cap:expr) => {
        let mut tag = ();
        let mut $name = unsafe {
            compact_arena::SmallArena::new(&mut tag, $cap)
        };
    };
}

/// Run a piece of code inside an arena
///
/// This may make it easier to see the scope (and was the old interface before
/// I managed to fix the soundness problems).
#[macro_export]
macro_rules! in_arena {
    ($name:ident, $e:expr) => {
        mk_arena!(arena);
        let $name = &mut arena;
        $e
    };
    ($name:ident / $cap:expr, $e:expr) => {
        mk_arena!(arena, $cap);
        let $name = &mut arena;
        $e
    };
}

/// Run code using a tiny arena. The indirection through this macro is
/// required to bind the indices to the arena.
///
/// # Examples
///
/// ```
///# use compact_arena::in_tiny_arena;
/// in_tiny_arena!(arena, {
///     let idx = arena.add(1usize);
///     assert_eq!(1, arena[idx]);
/// });
/// ```
#[macro_export]
macro_rules! in_tiny_arena {
    ($arena:ident, $e:expr) => {{
        let mut tag = ();
        let mut x = unsafe { compact_arena::TinyArena::new(&mut tag) };
        {
            let $arena = &mut x;
            $e
        }
    }};
}

/// Run code using a nano arena. The indirection through the macro is
/// required to bind the indices to the arena.
///
/// # Examples
///
/// ```
///# use compact_arena::in_nano_arena;
/// in_nano_arena!(arena, {
///     let idx = arena.add(1usize);
///     assert_eq!(1, arena[idx]);
/// });
/// ```
#[macro_export]
macro_rules! in_nano_arena {
    ($arena:ident, $e:expr) => {{
        let mut tag = ();
        let mut x = unsafe { compact_arena::NanoArena::new(&mut tag) };
        {
            let $arena = &mut x;
            $e
        }
    }};
}

impl<'tag, T> SmallArena<'tag, T> {
    /// create a new SmallArena. Don't do this manually. Use the
    /// [`in_arena`] macro instead.
    ///
    /// # Safety
    ///
    /// The whole tagged indexing trick relies on the `'tag` you give to this
    /// constructor. You must never use this value in another arena, lest you
    /// might be able to mix up the indices of the two, which could lead to
    /// out of bounds access and thus **Undefined Behavior**!
    pub unsafe fn new(_: &'tag mut (), capacity: usize) -> Self {
        SmallArena {
            tag: InvariantLifetime(PhantomData),
            data: Vec::with_capacity(capacity),
        }
    }

    /// Add an item to the arena, get an index or CapacityExceeded back.
    #[inline]
    pub fn try_add(&mut self, item: T)
    -> Result<Idx32<'tag>, CapacityExceeded<T>> {
        let i = self.data.len() as u32;
        if i == core::u32::MAX {
            return Err(CapacityExceeded(item));
        }
        self.data.push(item);
        Ok(Idx { index: i, tag: self.tag })
    }

    /// Add an item to the arena, get an index back.
    #[inline]
    pub fn add(&mut self, item: T) -> Idx32<'tag> {
        self.try_add(item).unwrap()
    }
}

impl<'tag, T> Index<Idx32<'tag>> for SmallArena<'tag, T> {
    type Output = T;

    /// Gets an immutable reference to the value at this index.
    #[inline]
    fn index(&self, i: Idx32<'tag>) -> &T {
        debug_assert!((i.index as usize) < self.data.len());
        unsafe { &self.data.get_unchecked(i.index as usize) }
    }
}

impl<'tag, T> IndexMut<Idx32<'tag>> for SmallArena<'tag, T> {
    /// Gets a mutable reference to the value at this index.
    #[inline]
    fn index_mut(&mut self, i: Idx32<'tag>) -> &mut T {
        debug_assert!((i.index as usize) < self.data.len());
        unsafe { self.data.get_unchecked_mut(i.index as usize) }
    }
}

const TINY_ARENA_ITEMS: usize = 65535;
const NANO_ARENA_ITEMS: usize = 255;

pub use tiny_arena::{TinyArena, NanoArena};

#[cfg(not(feature = "uninit"))]
mod tiny_arena {
    use crate::{CapacityExceeded, Idx16, Idx8, InvariantLifetime,
                TINY_ARENA_ITEMS, NANO_ARENA_ITEMS};
    use core::ops::{Index, IndexMut};
    use core::marker::PhantomData;

    /// A "tiny" arena containing <64K elements. This variant only works with
    /// types implementing `Default`.
    ///
    /// You will likely use this via the `in_tiny_arena` function.
    pub struct TinyArena<'tag, T> {
        tag: InvariantLifetime<'tag>,
        len: u16,
        data: [T; TINY_ARENA_ITEMS],
    }

    impl<'tag, T: Copy + Clone + Default> TinyArena<'tag, T> {
        /// create a new TinyArena. Don't do this manually. Use the
        /// [`in_tiny_arena`] macro instead.
        ///
        /// # Safety
        ///
        /// The whole tagged indexing trick relies on the `'tag` you give to
        /// this constructor. You must never use this value in another arena,
        /// lest you might be able to mix up the indices of the two, which
        /// could lead to out of bounds access and thus **Undefined Behavior**!
        pub unsafe fn new(_: &'tag mut ()) -> TinyArena<'tag, T> {
            TinyArena {
                tag: InvariantLifetime(PhantomData),
                data: [Default::default(); TINY_ARENA_ITEMS],
                len: 0
            }
        }

        /// Add an item to the arena, get an index or CapacityExceeded back.
        #[inline]
        pub fn try_add(&mut self, item: T)
        -> Result<Idx16<'tag>, CapacityExceeded<T>> {
            let i = self.len;
            if (i as usize) >= TINY_ARENA_ITEMS {
                return Err(CapacityExceeded(item));
            }
            self.data[i as usize] = item;
            self.len += 1;
            Ok(Idx16 { index: i, tag: self.tag })
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx16<'tag> {
            self.try_add(item).unwrap()
        }
    }

    impl<'tag, T> Index<Idx16<'tag>> for TinyArena<'tag, T> {
        type Output = T;
        fn index(&self, i: Idx16<'tag>) -> &T {
            debug_assert!(i.index < self.len);
            &self.data[i.index as usize]
        }
    }

    impl<'tag, T> IndexMut<Idx16<'tag>> for TinyArena<'tag, T> {
        fn index_mut(&mut self, i: Idx16<'tag>) -> &mut T {
            debug_assert!(i.index < self.len);
            &mut self.data[i.index as usize]
        }
    }

    /// A "nano" arena containing 255 elements. This variant only works with
    /// types implementing `Default`.
    ///
    /// You will likely use this via the `in_nano_arena` function.
    pub struct NanoArena<'tag, T> {
        tag: InvariantLifetime<'tag>,
        len: u8,
        data: [T; NANO_ARENA_ITEMS],
    }

    impl<'tag, T: Default + Copy> NanoArena<'tag, T> {
        /// create a new NanoArena. Don't do this manually. Use the
        /// [`in_nano_arena`] macro instead.
        ///
        /// # Safety
        ///
        /// The whole tagged indexing trick relies on the `'tag` you give to
        /// this constructor. You must never use this value in another arena,
        /// lest you might be able to mix up the indices of the two, which
        /// could lead to out of bounds access and thus **Undefined Behavior**!
        pub unsafe fn new(_: &'tag mut ()) -> NanoArena<'tag, T> {
            NanoArena {
                tag: InvariantLifetime(PhantomData),
                data: [Default::default(); NANO_ARENA_ITEMS],
                len: 0
            }
        }

        /// Add an item to the arena, get an index or CapacityExceeded back.
        #[inline]
        pub fn try_add(&mut self, item: T)
        -> Result<Idx8<'tag>, CapacityExceeded<T>> {
            let i = self.len;
            if (i as usize) >= NANO_ARENA_ITEMS {
                return Err(CapacityExceeded(item));
            }
            self.data[i as usize] = item;
            self.len += 1;
            Ok(Idx8 { index: i, tag: self.tag })
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx8<'tag> {
            self.try_add(item).unwrap()
        }
    }

    impl<'tag, T> Index<Idx8<'tag>> for NanoArena<'tag, T> {
        type Output = T;
        fn index(&self, i: Idx8<'tag>) -> &T {
            debug_assert!(i.index < self.len);
            &self.data[i.index as usize]
        }
    }

    impl<'tag, T> IndexMut<Idx8<'tag>> for NanoArena<'tag, T> {
        fn index_mut(&mut self, i: Idx8<'tag>) -> &mut T {
            debug_assert!(i.index < self.len);
            &mut self.data[i.index as usize]
        }
    }
}

#[cfg(feature = "uninit")]
mod tiny_arena {
    use crate::{CapacityExceeded, Idx16, Idx8, InvariantLifetime,
                TINY_ARENA_ITEMS, NANO_ARENA_ITEMS};
    use core::marker::PhantomData;
    use core::mem::{self, ManuallyDrop};
    use core::ops::{Index, IndexMut};

    /// A "tiny" arena containing <64K elements.
    pub struct TinyArena<'tag, T> {
        tag: InvariantLifetime<'tag>,
        len: u16,
        data: [ManuallyDrop<T>; TINY_ARENA_ITEMS],
    }

    impl<'tag, T> TinyArena<'tag, T> {
        /// create a new TinyArena
        pub unsafe fn new(_: &'tag mut ()) -> TinyArena<'tag, T> {
            TinyArena {
                tag: InvariantLifetime(PhantomData),
                data: mem::uninitialized(),
                len: 0
            }
        }

       /// Add an item to the arena, get an index or CapacityExceeded back.
        #[inline]
        pub fn try_add(&mut self, item: T)
        -> Result<Idx16<'tag>, CapacityExceeded<T>> {
            let i = self.len;
            if (i as usize) >= TINY_ARENA_ITEMS {
                return Err(CapacityExceeded(item));
            }
            self.data[i as usize] = ManuallyDrop::new(item);
            self.len += 1;
            Ok(Idx16 { index: i, tag: self.tag })
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx16<'tag> {
            self.try_add(item).unwrap()
        }
    }

    impl<'tag, T> Drop for TinyArena<'tag, T> {
        // dropping the arena drops all values
        fn drop(&mut self) {
            for i in 0..mem::replace(&mut self.len, 0) as usize {
                unsafe { ManuallyDrop::drop(&mut self.data[i]) };
            }
        }
    }

    impl<'tag, T> Index<Idx16<'tag>> for TinyArena<'tag, T> {
        type Output = T;
        fn index(&self, i: Idx16<'tag>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<'tag, T> IndexMut<Idx16<'tag>> for TinyArena<'tag, T> {
        fn index_mut(&mut self, i: Idx16<'tag>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }

    // nano arena

    /// A "nano" arena containing up to 255 elements.
    pub struct NanoArena<'tag, T> {
        tag: InvariantLifetime<'tag>,
        len: u8,
        data: [ManuallyDrop<T>; NANO_ARENA_ITEMS],
    }

    impl<'tag, T> NanoArena<'tag, T> {
        /// create a new NanoArena. Don't do this manually. Use the
        /// [`in_nano_arena`] macro instead.
        ///
        /// # Safety
        ///
        /// The whole tagged indexing trick relies on the `'tag` you give to
        /// this constructor. You must never use this value in another arena,
        /// lest you might be able to mix up the indices of the two, which
        /// could lead to out of bounds access and thus **Undefined Behavior**!
        pub unsafe fn new(_: &'tag mut ()) -> NanoArena<'tag, T> {
            NanoArena {
                tag: InvariantLifetime(PhantomData),
                data: mem::uninitialized(),
                len: 0,
            }
        }

        /// Add an item to the arena, get an index or CapacityExceeded back.
        #[inline]
        pub fn try_add(&mut self, item: T)
        -> Result<Idx8<'tag>, CapacityExceeded<T>> {
            let i = self.len;
            if (i as usize) >= NANO_ARENA_ITEMS {
                return Err(CapacityExceeded(item));
            }
            self.data[i as usize] = ManuallyDrop::new(item);
            self.len += 1;
            Ok(Idx8 { index: i, tag: self.tag })
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx8<'tag> {
            self.try_add(item).unwrap()
        }
    }

    impl<'tag, T> Drop for NanoArena<'tag, T> {
        // dropping the arena drops all values
        fn drop(&mut self) {
            for i in 0..mem::replace(&mut self.len, 0) as usize {
                unsafe { ManuallyDrop::drop(&mut self.data[i]) };
            }
        }
    }

    impl<'tag, T> Index<Idx8<'tag>> for NanoArena<'tag, T> {
        type Output = T;

        /// Gets an immutable reference to the value at this index
        fn index(&self, i: Idx8<'tag>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<'tag, T> IndexMut<Idx8<'tag>> for NanoArena<'tag, T> {
        /// Gets a mutable reference to the value at this index
        fn index_mut(&mut self, i: Idx8<'tag>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }
}
