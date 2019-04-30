extern crate compact_arena;

use compact_arena::{mk_nano_arena, Idx8};

fn recursive(idx: Option<Idx8<'_>>) {
    mk_nano_arena!(arena); // `tag` does not live long enough
    if let Some(idx) = idx {
        assert_eq!("hello", arena[idx]);
    } else {
        recursive(Some(arena.add("hello")));
    }
}

fn main() {
    recursive(None);
}
