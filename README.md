wasm-redex
----------

This is a (unofficial) Redex model of the WebAssembly formalism from the paper

  ["Bringing the Web up to Speed with WebAssembly"](https://dl.acm.org/citation.cfm?doid=3062341.3062363) by Haas et al.

It aims to model the reduction semantics of wasm but it doesn't quite cover
everything in the paper. It's missing the following at least:

  * module instantiation semantics
  * static type system / validation

and of course likely has various bugs.

See also: the wasm [reference interpreter & spec](https://github.com/WebAssembly/spec).

---

Copyright © 2019 Asumu Takikawa

Licensed under Apache License 2.0, the same as the [reference interpreter & tests](https://github.com/WebAssembly/spec/blob/master/LICENSE).

Attribution: many of the tests are derived from the reference tests.
