Hindley-Milner Type System
===

A pocket-sized implementation of a functional language with a [Hindley-Milner type system](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system).


Content
---

- [Lexer](./src/lexer.rs)
- [Parser](./src/parser.rs)
- [Abstract Syntax Tree](./src/ast.rs)
- [Types](./src/type.rs)
- [Unification Algorithm](./src/unification.rs)
- [Type Inference](./src/type_inference.rs)


Build and Test
---

```
cargo build
cargo test
```


License
-------

This project is licensed under the BSD-3-Clause license - see the [LICENSE.md](LICENSE.md) file for details.
