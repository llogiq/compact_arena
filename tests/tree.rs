use compact_arena::{SmallArena, in_arena, Idx32};

struct Tree<B>(Option<(Idx32<B>, Idx32<B>)>);

fn bottom_up_tree<B>(arena: &mut SmallArena<Tree<B>, B>, depth: usize)
-> Idx32<B> {
    let i = arena.add(Tree(None));
    if depth > 0 {
        let d = depth - 1;
        let left = bottom_up_tree(arena, d);
        let right = bottom_up_tree(arena, d);
        arena[i].0 = Some((left, right));
    }
    i
}

#[test]
fn tree() {
    in_arena!(arena, bottom_up_tree(arena, 3));
}
