# compact_arena

This is a crate with arenas that work with indices. Currently there are three
types: `SmallArena` uses 32-bit indices and can hold up to 2³² objects.
`TinyArena` uses 16-bit indices and can hold up to 65535 objects, regardless
of object size. `NanoArena` uses 8-bit indices and contain up to 255 objects.

This can conserve memory in scenarios where we have a large-ish number of
relations between objects, e.g. in graph algorithms. `NanoArena` is likely
most useful in embedded scenarios.

## Usage:

Add the following dependency to your `Cargo.toml`

```toml
compact_arena = "0.2.1"
```

By default, the `TinyArena` uses no unsafe code to maintain storage, but
requires the stored types to be `Default + Copy`. To change this, you can use
the `uninit` feature to enable usage on all types with a bit more unsafe code:

```toml
compact_arena = { version = "0.2.1", features = ["uninit"] }
```

In your code, use it as follows:

```rust
use compact_arena::in_arena;

in_arena!(arena, {
    let hello = arena.add("Hello");
    let world = arena.add("World");
    println!("{}, {}!", arena[hello], arena[world]);
});
```

For further information, please read the [documentation](https://docs.rs/compact_arena).

# License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
