
#[cfg(not(miri))] // this will take too much time for miri
#[test]
fn add_65536_objects() {
    use compact_arena::in_tiny_arena;

    in_tiny_arena!(arena, {
        for _ in 0..=65535 {
            arena.add(42); // all should be ok
        }
    });
}

#[cfg(not(miri))] // miri will fail due to unsafe { panic_impl(&pi) }
#[test]
#[should_panic(expected = "Capacity Exceeded")]
fn add_65537_objects() {
    use compact_arena::in_tiny_arena;

    in_tiny_arena!(arena, {
        for _ in 0..=65535 {
            arena.add(42); // all should be ok
        }
        arena.add(65537); // should panic
    });
}
