(** * Core

This file provides the main interface of the RingLike library. It gathers
all the relevant modules, so users only need to:
<<
    Require Import RingLike.Core.
>>

## Supported structures

This library is designed a general support for semirings, rings, fields,
i.e. algebraic structures holding addition, multiplication and, possible
negation and inverse, such as:

- ℕ, ℤ, ℚ, ℝ, ℂ
- ℤ/nℤ
- polynomials
- matrices
- ideals

## Partial operations

Even when a structure lacks full inverses, it can still provide "partial
operations" that behave like subtraction or division in restricted settings.

- A semiring like ℕ has no negation, but it may provide a subtraction function
  `sub` such that:
<<
      ∀ a b, a + b - b = a
>>

That is, subtraction "undoes" addition **on the right**. But outside this
context, the value of `a - b` is not defined by the interface, and no
properties can be derived.

- Similarly, a ring like ℤ may not have multiplicative inverses, but may
  define a division function `quot` such that:
<<
      ∀ a b, a * b / b = a
>>

Again, this only captures cancellation on the right, and says nothing about
the actual value of `a / b`.

These operations are **not** inverses, and do **not** imply any order or
totality.

## How structures are defined

A structure is "ring-like" if it supports operations such as addition and
multiplication, possibly with an additive inverse or a multiplicative
inverse. Instead of using fixed categories like "ring" or "field", we use
a flexible encoding with two optional fields:
<<
    rngl_opt_opp_or_subt : option (sum (T → T) (T → T → T))
    rngl_opt_inv_or_quot : option (sum (T → T) (T → T → T))
>>

These allow three cases for each:

- None: neither an inverse nor a subtraction/division exists.
- Some (inl f): a genuine inverse function exists (e.g., -x or 1/x).
- Some (inr f): an isolated operation exists (e.g., x - y without -x).

## Standard algebraic cases

- A semiring (ℕ): no inverse (opp/inv), but possibly subtraction/division
  operations.
- A ring (ℤ): has additive inverse, but not necessarily multiplicative.
- A field (ℚ, ℝ, ℂ): both additive and multiplicative inverses exist.

We define two booleans:

- rngl_has_opp ≡ rngl_opt_opp_or_subt = Some (inl _)
- rngl_has_inv ≡ rngl_opt_inv_or_quot = Some (inl _)
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
