extern crate compact_arena;

use compact_arena::in_nano_arena;

fn main() {
    in_nano_arena!(a, {
        in_nano_arena!(b, {
            let _ = a.add(1usize);
            let x = a.add(1usize);
            let y = b.add(1usize);
            let _ = b[x];
        })
    });
}
