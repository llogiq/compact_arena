extern crate crossbeam_utils;

use compact_arena::mk_nano_arena;
use crossbeam_utils::thread::scope;

// With crossbeam's `scope`d threads, it is even possible to share an arena
// and its indices between multiple threads.
#[test]
fn test_scoped_arena() {
    mk_nano_arena!(arena);
    let i = arena.add(1usize);
    let v = scope(|s| {
        // spawn a thread using both the arena and an existing index
        let t = s.spawn(|_| {
            let u = arena[i];
            arena.add(u + 1)
        });
        // join it, receiving a new index from the thread
        t.join().unwrap()
    })
    .unwrap();
    assert_eq!(2, arena[v]);
}
