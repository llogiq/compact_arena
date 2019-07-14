use compact_arena::{in_tiny_arena, mk_tiny_arena};

#[cfg(not(miri))] // this will take too much time for miri
#[test]
fn add_65536_objects() {
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
    in_tiny_arena!(arena, {
        for _ in 0..=65535 {
            arena.add(42); // all should be ok
        }
        arena.add(65537); // should panic
    });
}

#[test]
fn two_tiny_arenas() {
    std::thread::Builder::new().stack_size(32 * 1024 * 1024).spawn(|| {
        assert_eq!(3, in_tiny_arena!(a, {
            in_tiny_arena!(b, {
                let x = a.add(1usize);
                let y = b.add(2usize);
                a[x] + b[y]
            })
        }))
    }).unwrap().join().unwrap();
}

#[test]
fn two_tiny_arenas_one_scope() {
    std::thread::Builder::new().stack_size(32 * 1024 * 1024).spawn(|| {
        mk_tiny_arena!(a);
        mk_tiny_arena!(b);
        let x = a.add(1usize);
        let y = b.add(2usize);
        assert_eq!(3, a[x] + b[y])
    }).unwrap().join().unwrap();
}
