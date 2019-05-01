extern crate compact_arena;

use compact_arena::mk_nano_arena;

fn main() {
    mk_nano_arena!(a);
    mk_nano_arena!(b);
    let i = a.add(1usize);
    let j = b.add(1usize);
    let _ = b[i];
}
