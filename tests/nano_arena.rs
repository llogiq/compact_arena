use compact_arena::in_nano_arena;

#[test]
fn add_256_objects() {
    in_nano_arena!(arena, {
        for _ in 0..=255 {
            arena.add(42); // all should be ok
        }
    });
}

#[cfg(not(miri))] // miri will fail due to unsafe { panic_impl(&pi) }
#[test]
#[should_panic(expected = "Capacity Exceeded")]
fn add_257_objects() {
    in_nano_arena!(arena, {
        for _ in 0..=255 {
            arena.add(42); // all should be ok
        }
        arena.add(257); // should panic
    });
}
