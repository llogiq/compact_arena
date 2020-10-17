use compact_arena::{in_nano_arena, mk_nano_arena};

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

#[test]
fn two_nano_arenas() {
    assert_eq!(
        3,
        in_nano_arena!(a, {
            in_nano_arena!(b, {
                let x = a.add(1usize);
                let y = b.add(2usize);
                a[x] + b[y]
            })
        })
    );
}

#[test]
fn two_nano_arenas_one_scope() {
    mk_nano_arena!(a);
    mk_nano_arena!(b);
    let x = a.add(1usize);
    let y = b.add(2usize);
    assert_eq!(3, a[x] + b[y]);
}
