#[cfg(feature = "alloc")]
use compact_arena::{SmallArena as Arena, mk_arena, Idx32 as Idx};

#[cfg(not(feature = "alloc"))]
use compact_arena::{NanoArena as Arena, mk_nano_arena as mk_arena, Idx8 as Idx};

#[derive(Default, Copy, Clone)]
struct Tree<'tag>(Option<(Idx<'tag>, Idx<'tag>)>);

fn top_down_tree<'tag>(arena: &mut Arena<'tag, Tree<'tag>>, d: usize)
-> Idx<'tag> {
    let children = if d > 0 {
        Some((top_down_tree(arena, d - 1), top_down_tree(arena, d - 1)))
    } else {
        None
    };
    arena.add(Tree(children))
}

fn bottom_up_tree<'tag>(arena: &mut Arena<'tag, Tree<'tag>>, depth: usize)
-> Idx<'tag> {
    let i = arena.add(Tree(None));
    if depth > 0 {
        let d = depth - 1;
        let left = bottom_up_tree(arena, d);
        let right = bottom_up_tree(arena, d);
        arena[i].0 = Some((left, right));
    }
    i
}

fn count<'tag>(a: &Arena<'tag, Tree<'tag>>, i: Idx<'tag>) -> usize {
    if let Some((left, right)) = a[i].0 {
        1 + count(a, left) + count(a, right)
    } else {
        1
    }
}

#[test]
fn tree() {
    mk_arena!(arena);
    let top_down = top_down_tree(&mut arena, 3);
    let bottom_up = bottom_up_tree(&mut arena, 3);
    assert_eq!(count(&arena, top_down), count(&arena, bottom_up));
}
