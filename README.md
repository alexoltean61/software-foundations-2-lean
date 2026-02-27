# Software Foundations V2 in Lean

Welcome! This repository focuses on porting [Software Foundations Vol. 2: Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/index.html), to [Lean 4](https://lean-lang.org/).

We do this as lab work for the **Program Verification** master's course at the [Faculty of Mathematics & Computer Science, Univ. of Bucharest](https://fmi.unibuc.ro/).

### Building
Before you start, make sure you have [Lean installed](https://lean-lang.org/install/) in your environment.

1. Clone this repository.
2. From your cloned directory, run `lake exe cache get`. This will fetch a compressed version of the `Mathlib` library, which would normally be huge.
3. Run `lake build`.