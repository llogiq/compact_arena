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
//! Use the `in_arena` and similar methods to run code within the scope of an
//! arena:
//!
//! # Examples
//!
//! ```
//!# use compact_arena::in_arena;
//! in_arena!(arena, {
//!     let idx = arena.add(1usize);
//!     assert_eq!(1, arena[idx]);
//! });
//! ```
//!
//! You can use `in_sized_arena` to change the initial size of the backing
//! memory:
//!
//! ```
//!# #[allow(dead_code)]
//!# use compact_arena::in_arena;
//! in_arena!(arena / 1, {
//!     ..
//!# ; arena.add(1usize);
//! });
//! ```
//!
//! You can nest calls to work with multiple arenas:
//!
//! ```
//!# #[allow(dead_code)]
//!# use compact_arena::in_arena;
//! in_arena!(a / 1, {
//!     in_arena!(b / 1, {
//!         ..
//!# ; a.add(1u32); b.add(1u32);
//!     })
//! });
//! ```
//!
//! The compiler gives you a type error if you mix up arenas:
//!
//! ```compile_fail
//!# use compact_arena::in_arena;
//! in_arena!(a / 1, {
//!     in_arena!(b / 1, {
//!         let i = a.add(1usize);
//!         let _ = b[i];
//!     })
//! });
//! ```
//!
//! The indices should not be able to escape the `in_arena` call
//!
//! ```compile_fail
//!# use compact_arena::in_arena;
//! let idx = in_arena!(arena / 1, arena.add(1usize));
//! assert!(core::mem::size_of_val(&a) == 4);
//! ```
//!
//! Also, arenas may not be instantiated recursively:
//!
//! ```compile_fail
//!# use compact_arena::in_arena;
//! fn recursive(idx: Option<Box<dyn std::any::Any>>) {
//!     in_arena!(arena, {
//!         if let Some(idx) = idx {
//!             println!("{}", arena[*idx.downcast().unwrap()]);
//!         } else {
//!             recursive(Some(Box::new(arena.add("hello"))));
//!         }
//!     });
//! }
//! recursive(None);
//! ```

use core::ops::{Index, IndexMut};
use core::marker::PhantomData;

/// An index into the arena. You will not directly use this type, but one of
/// the aliases this crate provides (`Idx32`, `Idx16` or `Idx8`).
///
/// The only way to get an index into an arena is to `add` a value to it. With
/// an `Idx` you can index or mutably index into the arena to observe or mutate
/// the value.
#[derive(PartialOrd, PartialEq, Eq)]
pub struct Idx<I: Copy + Clone, B> {
    index: I,
    tag: PhantomData<B>,
}

impl<I: Copy + Clone, B> Copy for Idx<I, B> { }
impl<I: Copy + Clone, B> Clone for Idx<I, B> {
    fn clone(&self) -> Self {
        *self
    }
}

/// The index type for a small arena is 32 bits large. You will usually get the
/// index from the arena and use it by indexing, e.g. `arena[index]`.
///
/// # Examples
///
/// ```
///# use {compact_arena::Idx32, core::mem::size_of};
/// assert_eq!(size_of::<Idx32<String>>(), size_of::<u32>());
/// ```
pub type Idx32<B> = Idx<u32, B>;

/// The index type for a tiny arena is 16 bits large. You will usually get the
/// index from the arena and use it by indexing, e.g. `arena[index]`.
///
/// # Examples:
///
/// ```
///# use {compact_arena::Idx16, core::mem::size_of};
/// assert_eq!(size_of::<Idx16<usize>>(), size_of::<u16>());
/// ```
pub type Idx16<B> = Idx<u16, B>;

/// The index type for a nano arena is 8 bits large. You will usually get the
/// index from the arena and use it by indexing, e.g. `arena[index]`.
///
/// # Examples:
///
/// ```
///# use {compact_arena::Idx8, core::mem::size_of};
/// assert_eq!(size_of::<Idx8<i128>>(), size_of::<u8>());
/// ```
pub type Idx8<B> = Idx<u8, B>;

/// A "Small" arena based on a resizable slice (i.e. a `Vec`) that can be
/// indexed with 32-bit `Idx32`s. This can help reduce memory overhead when
/// using many pointer-heavy objects on 64-bit systems.
///
/// You will usually use this type by calling `in_arena` or similar functions.
pub struct SmallArena<T, B> {
    tag: PhantomData<B>,
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
///# use compact_arena::in_arena;
/// assert_eq!(in_arena!(arena, {
///     let half = arena.add(21);
///     arena[half] + arena[half]
/// }), 42);
/// ```
///
/// You can also specify an initial size after the arena identifier:
///
/// ```
///# #[allow(dead_code)]
///# use compact_arena::in_arena;
/// in_arena!(arena / 65536, {
///# arena.add(2usize);
///     ..
/// });
/// ```
#[macro_export]
macro_rules! in_arena {
    ($arena:ident, $e:expr) => { in_arena!($arena / 1024*1024, $e) };
    ($arena:ident / $cap:expr, $e:expr) => {
        {
            struct Tag;
            let mut tag = Tag;
            let mut x = unsafe { compact_arena::SmallArena::new(&mut tag, $cap) };
            {
                let $arena = &mut x;
                $e
            }
        }
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
    ($arena:ident, $e:expr) => {        {
            #[derive(Copy, Clone)]
            struct Tag;

            let mut x = unsafe { compact_arena::TinyArena::new(Tag) };
            {
                let $arena = &mut x;
                $e
            }
        }
    };
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
    ($arena:ident, $e:expr) => {        {
            #[derive(Copy, Clone)]
            struct Tag;

            let mut x = unsafe { compact_arena::NanoArena::new(Tag) };
            {
                let $arena = &mut x;
                $e
            }
        }
    };
}

impl<T, B> SmallArena<T, B> {
    /// create a new SmallArena. Don't do this manually. Use the
    /// [`in_arena`] macro instead.
    ///
    /// # Safety
    ///
    /// The whole tagged indexing trick relies on the `B` type you give to this
    /// constructor. You must never use this type in another arena, lest you
    /// might be able to mix up the indices of the two, which could lead to
    /// out of bounds access and thus **Undefined Behavior**!
    pub unsafe fn new(_: B, capacity: usize) -> SmallArena<T, B> {
        SmallArena {
            tag: PhantomData,
            data: Vec::with_capacity(capacity),
        }
    }

    /// Add an item to the arena, get an index back.
    #[inline]
    pub fn add(&mut self, item: T) -> Idx32<B> {
        let i = self.data.len() as u32;
        self.data.push(item);
        Idx { index: i, tag: self.tag }
    }
}

impl<B, T> Index<Idx32<B>> for SmallArena<T, B> {
    type Output = T;

    /// Gets an immutable reference to the value at this index.
    #[inline]
    fn index(&self, i: Idx32<B>) -> &T {
        debug_assert!((i.index as usize) < self.data.len());
        unsafe { &self.data.get_unchecked(i.index as usize) }
    }
}

impl<B, T> IndexMut<Idx32<B>> for SmallArena<T, B> {
    /// Gets a mutable reference to the value at this index.
    #[inline]
    fn index_mut(&mut self, i: Idx32<B>) -> &mut T {
        debug_assert!((i.index as usize) < self.data.len());
        unsafe { self.data.get_unchecked_mut(i.index as usize) }
    }
}

const TINY_ARENA_ITEMS: usize = 65535;
const NANO_ARENA_ITEMS: usize = 255;

pub use tiny_arena::{TinyArena, NanoArena};

#[cfg(not(feature = "uninit"))]
mod tiny_arena {
    use crate::{Idx16, Idx8, TINY_ARENA_ITEMS, NANO_ARENA_ITEMS};
    use core::ops::{Index, IndexMut};
    use core::marker::PhantomData;

    /// A "tiny" arena containing <64K elements. This variant only works with
    /// types implementing `Default`.
    ///
    /// You will likely use this via the `in_tiny_arena` function.
    pub struct TinyArena<T, B> {
        tag: PhantomData<B>,
        len: u16,
        data: [T; TINY_ARENA_ITEMS],
    }

    impl<T: Copy + Clone + Default, B> TinyArena<T, B> {
        /// create a new TinyArena. Don't do this manually. Use the
        /// [`in_tiny_arena`] macro instead.
        ///
        /// # Safety
        ///
        /// The whole tagged indexing trick relies on the `B` type you give to
        /// this constructor. You must never use this type in another arena,
        /// lest you might be able to mix up the indices of the two, which
        /// could lead to out of bounds access and thus **Undefined Behavior**!
        pub unsafe fn new(_: B) -> TinyArena<T, B> {
            TinyArena {
                tag: PhantomData,
                data: [Default::default(); TINY_ARENA_ITEMS],
                len: 0
            }
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx16<B> {
            let i = self.len;
            assert!((i as usize) < TINY_ARENA_ITEMS);
            self.data[i as usize] = item;
            self.len += 1;
            Idx16 { tag: self.tag, index: i }
        }
    }

    impl<T, B> Index<Idx16<B>> for TinyArena<T, B> {
        type Output = T;
        fn index(&self, i: Idx16<B>) -> &T {
            debug_assert!(i.index < self.len);
            &self.data[i.index as usize]
        }
    }

    impl<T, B> IndexMut<Idx16<B>> for TinyArena<T, B> {
        fn index_mut(&mut self, i: Idx16<B>) -> &mut T {
            debug_assert!(i.index < self.len);
            &mut self.data[i.index as usize]
        }
    }

    /// A "nano" arena containing 255 elements. This variant only works with
    /// types implementing `Default`.
    ///
    /// You will likely use this via the `in_nano_arena` function.
    pub struct NanoArena<T, B> {
        tag: PhantomData<B>,
        len: u8,
        data: [T; NANO_ARENA_ITEMS],
    }

    impl<T: Default + Copy, B> NanoArena<T, B> {
        /// create a new NanoArena. Don't do this manually. Use the
        /// [`in_nano_arena`] macro instead.
        ///
        /// # Safety
        ///
        /// The whole tagged indexing trick relies on the `B` type you give to
        /// this constructor. You must never use this type in another arena,
        /// lest you might be able to mix up the indices of the two, which
        /// could lead to out of bounds access and thus **Undefined Behavior**!
        pub unsafe fn new(_: B) -> NanoArena<T, B> {
            NanoArena {
                tag: PhantomData,
                data: [Default::default(); NANO_ARENA_ITEMS],
                len: 0
            }
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx8<B> {
            let i = self.len;
            assert!((i as usize) < NANO_ARENA_ITEMS);
            self.data[i as usize] = item;
            self.len += 1;
            Idx8 { tag: self.tag, index: i }
        }
    }

    impl<T, B> Index<Idx8<B>> for NanoArena<T, B> {
        type Output = T;
        fn index(&self, i: Idx8<B>) -> &T {
            debug_assert!(i.index < self.len);
            &self.data[i.index as usize]
        }
    }

    impl<T, B> IndexMut<Idx8<B>> for NanoArena<T, B> {
        fn index_mut(&mut self, i: Idx8<B>) -> &mut T {
            debug_assert!(i.index < self.len);
            &mut self.data[i.index as usize]
        }
    }
}

#[cfg(feature = "uninit")]
mod tiny_arena {
    use crate::{Idx16, Idx8, TINY_ARENA_ITEMS, NANO_ARENA_ITEMS};
    use core::marker::PhantomData;
    use core::mem::{self, ManuallyDrop};
    use core::ops::{Index, IndexMut};

    /// A "tiny" arena containing <64K elements.
    pub struct TinyArena<T, B> {
        tag: PhantomData<B>,
        len: u16,
        data: [ManuallyDrop<T>; TINY_ARENA_ITEMS],
    }

    impl<T, B> TinyArena<T, B> {
        /// create a new TinyArena
        pub unsafe fn new(_: B) -> TinyArena<T, B> {
            TinyArena {
                tag: PhantomData,
                data: mem::uninitialized(),
                len: 0
            }
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx16<B> {
            let i = self.len;
            self.data[i as usize] = ManuallyDrop::new(item);
            self.len += 1;
            Idx16 { tag: self.tag, index: i }
        }
    }

    impl<T, B> Drop for TinyArena<T, B> {
        // dropping the arena drops all values
        fn drop(&mut self) {
            for i in 0..self.len as usize {
                unsafe { ManuallyDrop::drop(&mut self.data[i]) };
            }
            self.len = 0;
        }
    }

    impl<T, B> Index<Idx16<B>> for TinyArena<T, B> {
        type Output = T;
        fn index(&self, i: Idx16<B>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<T, B> IndexMut<Idx16<B>> for TinyArena<T, B> {
        fn index_mut(&mut self, i: Idx16<B>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }

    // nano arena

    /// A "nano" arena containing up to 255 elements.
    pub struct NanoArena<T, B> {
        tag: PhantomData<B>,
        len: u8,
        data: [ManuallyDrop<T>; NANO_ARENA_ITEMS],
    }

    impl<T, B> NanoArena<T, B> {
        /// create a new NanoArena. Don't do this manually. Use the
        /// [`in_nano_arena`] macro instead.
        ///
        /// # Safety
        ///
        /// The whole tagged indexing trick relies on the `B` type you give to
        /// this constructor. You must never use this type in another arena,
        /// lest you might be able to mix up the indices of the two, which
        /// could lead to out of bounds access and thus **Undefined Behavior**!
        pub unsafe fn new(_: B) -> NanoArena<T, B> {
            NanoArena {
                tag: PhantomData,
                data: mem::uninitialized(),
                len: 0,
            }
        }

        /// Add an item to the arena, get an index back
        pub fn add(&mut self, item: T) -> Idx8<B> {
            let i = self.len;
            self.data[i as usize] = ManuallyDrop::new(item);
            self.len += 1;
            Idx8 { tag: self.tag, index: i }
        }
    }

    impl<T, B> Drop for NanoArena<T, B> {
        // dropping the arena drops all values
        fn drop(&mut self) {
            for i in 0..self.len as usize {
                unsafe { ManuallyDrop::drop(&mut self.data[i]) };
            }
            self.len = 0;
        }
    }

    impl<T, B> Index<Idx8<B>> for NanoArena<T, B> {
        type Output = T;

        /// Gets an immutable reference to the value at this index
        fn index(&self, i: Idx8<B>) -> &T {
            &self.data[i.index as usize]
        }
    }

    impl<T, B> IndexMut<Idx8<B>> for NanoArena<T, B> {
        /// Gets a mutable reference to the value at this index
        fn index_mut(&mut self, i: Idx8<B>) -> &mut T {
            &mut self.data[i.index as usize]
        }
    }
}
