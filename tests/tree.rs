use compact_arena::{SmallArena, mk_arena, Idx32};

struct Tree<'tag>(Option<(Idx32<'tag>, Idx32<'tag>)>);

fn top_down_tree<'tag>(arena: &mut SmallArena<'tag, Tree<'tag>>, d: usize)
-> Idx32<'tag> {
    let children = if d > 0 {
        Some((top_down_tree(arena, d - 1), top_down_tree(arena, d - 1)))
    } else {
        None
    };
    arena.add(Tree(children))
}

fn bottom_up_tree<'tag>(arena: &mut SmallArena<'tag, Tree<'tag>>, depth: usize)
-> Idx32<'tag> {
    let i = arena.add(Tree(None));
    if depth > 0 {
        let d = depth - 1;
        let left = bottom_up_tree(arena, d);
        let right = bottom_up_tree(arena, d);
        arena[i].0 = Some((left, right));
    }
    i
}

fn count<'tag>(a: &SmallArena<'tag, Tree<'tag>>, i: Idx32<'tag>) -> usize {
    if let Some((left, right)) = a[i].0 {
        1 + count(a, left) + count(a, right)
    } else {
        1
    }
}

#[test]
fn tree() {
    mk_arena!(arena, 32);
    let top_down = top_down_tree(&mut arena, 3);
    let bottom_up = bottom_up_tree(&mut arena, 3);
    assert_eq!(count(&arena, top_down), count(&arena, bottom_up));
}
