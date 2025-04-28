⚠️ This library is currently under construction. It may change
frequently and is not ready for public use yet.

# rocq_ring_like

This library defines a general algebraic structure called "Ring Like"
("espèce d'anneau" in French), which covers semirings, rings, fields,
and other variants via boolean parameters controlling the presence of
additive inverses, multiplicative inverses, commutativity,
completeness, archimedean property, etc.

It also provides many theorems on these structures, and basic syntax
for sums, products, maximum.

This project is developed with [Rocq](https://github.com/rocq-prover/rocq)
version 9.0.0 or later.

## Installation

To install this project via `opam`, use:

```bash
opam pin add rocq_ring_like https://github.com/roglo/rocq_ring_like.git
opam install rocq_ring_like
