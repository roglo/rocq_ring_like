(** * RingLike

The **RingLike** library provides a general interface for algebraic structures such as semirings, rings, and fields — but is not limited to those.

It is designed to be **flexible** and **modular**, allowing for
representations of many kinds of algebraic systems, including:
- the standard number systems ℕ, ℤ, ℚ, ℝ, ℂ,
- modular rings like ℤ/nℤ,
- algebraic structures like polynomials, matrices, ideals, etc.

Rather than being tailored only for textbook algebraic structures,
RingLike supports partial or nonstandard operations, making it
suitable for abstract algebra, computer algebra systems, and
formalization of custom structures.

This library defines a general algebraic interface — called a
"ring-like structure" — that captures the behavior of **semirings**,
**rings**, and **fields** in a unified way.

## Usage

To use the interface, import the main entry point:
<<
    Require Import RingLike.Core.
>>

## Basic idea

Mathematically, we distinguish:
- A **semiring** (e.g., ℕ): addition and multiplication, but no additive inverse or division.
- A **ring** (e.g., ℤ): has additive inverses (negation), but not necessarily multiplicative inverses.
- A **field** (e.g., ℚ): has both additive and multiplicative inverses.

These are represented by two boolean flags:
- `rngl_has_opp` — true when the structure has an additive inverse (negation).
- `rngl_has_inv` — true when the structure has a multiplicative inverse (reciprocal).

## Summary table

<<
  Structure      | rngl_has_opp | rngl_has_inv
  -------------- | -------------|--------------
  Semiring (ℕ)   | false        | false
  Ring (ℤ)       | true         | false
  Field (ℚ)      | true         | true
>>

## Partial operations

Even when a structure lacks full inverses, it can still provide **partial operations** 
that behave like subtraction or division in restricted settings.

- A semiring like ℕ has no negation, but it may provide a subtraction function `sub` such that:
  
      ∀ a b, a + b - b = a

  That is, subtraction "undoes" addition **on the right**. But outside this context, 
  the value of `a - b` is not defined by the interface, and no properties can be derived.

- Similarly, a ring like ℤ may not have multiplicative inverses, but may define a division function `quot` such that:
  
      ∀ a b, a * b / b = a

  Again, this only captures cancellation on the right, and says nothing about the actual
  value of `a / b`.

These operations are **not** inverses, and do **not** imply any order or totality. 
They are modeled via:

<<
  rngl_opt_opp_or_subt : option (sum (T → T) (T → T → T));
  rngl_opt_inv_or_quot : option (sum (T → T) (T → T → T));
>>

- `Some (inl f)` means a true inverse (e.g., negation or reciprocal).
- `Some (inr f)` means an isolated operation satisfying only a cancellation law.
- `None` means no such operation is defined.

This allows us to represent ℕ with `sub`, ℤ with `quot`, and ℚ with full inverses, 
using a uniform interface.

## Internals

The main structure is defined as a `record` containing operations and properties. Many auxiliary predicates are defined to extract the shape of the structure (e.g., `rngl_has_opp`)

## Entry point

To use the library, import the core module:

<<
Require Import RingLike.Core.
>>
*)

Require Export Structures.
Require Export Order.
Require Export Add.
Require Export Mul.
Require Export Div.
Require Export Add_with_order.
Require Export Mul_with_order.
Require Export Div_with_order.
Require Export Distances.
