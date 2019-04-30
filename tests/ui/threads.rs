extern crate compact_arena;

use std::{thread, sync::mpsc::{channel, Receiver, Sender}};
use compact_arena::{mk_tiny_arena, Idx16};

fn mixup(s: Option<Sender<Idx16<'_>>>, r: Option<Receiver<Idx16<'_>>>) {
    mk_tiny_arena!(arena);
    match (s, r) {
        (Some(s), None) => s.send(arena.add(1usize)).unwrap(),
        (None, Some(r)) => assert_eq!(1, arena[r.recv().unwrap()]),
        _ => unreachable!()
    }
}

fn main() {
    let (s, r) = channel();
    let st = thread::spawn(|| mixup(Some(s), None));
    let rt = thread::spawn(|| mixup(None, Some(r)));
    st.join().unwrap();
    rt.join().unwrap();
}
