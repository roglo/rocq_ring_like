(** * RingLike.Core

This library is designed to support semirings, rings, fields, and, in
general, algebraic structures containing addition and multiplication and,
optionally, opposite and inverse. For example, it can represent:

- ℕ, ℤ, ℚ, ℝ, ℂ
- ℤ/nℤ
- polynomials
- square matrices
- ideals

Such a general structure is here called a "ring-like".

## Subtraction and Division

In mathematics, subtraction is usually defined as the addition of the
opposite:
<<
      a - b ::= a + (- b)
>>
and the division as the multiplication of the inverse:
<<
      a / b ::= a * (1 / b)
>>

However, some sets can have a subtraction and/or an inverse as partially
defined functions. For example, ℕ, the set of naturals has its own
subtraction and its own division (quotient of euclidean division).

The library RingLike can represent these functions when they exist.
It requires that the partially defined subtraction must have the main
following property:
<<
      ∀ a b, a + b - b = a
>>
and the partially defined division:
<<
      ∀ a b, b ≠ 0 → a * b / b = a
>>

For example, in mathematics, the set of naturals ℕ has a subtraction
and a euclidean division. In Rocq library, the type "nat", representing
this set, provides a subtraction Nat.sub and a division Nat.div having
both the above properties.

If we compute [5-3] in ℕ, we get [2]. On the other hand,
[3-5] has no value. In the Rocq type "nat", the value of this
expression is also [2], but [3-5] is computable and returns
[0]. As a ring-like, this expression is equal to [2+3-3]
and, by the first above property, can be reduced to [2]. But [3-5]
is not reducable, its value is undefined.

The same way, [12/3] is [4] in the set ℕ and also in the Rocq
type "nat". As a ring-like, it is equal to [4*3/3] and its
value is therefore [4] too, by the second above property. However,
the expression [7/3] has no value in ℕ, since [7] is not divisible
by [3]. In the type "nat", it is the quotient of the euclidean division,
i.e. [2]. But as a ring-like, this expression is not reducable, its value
is undefined.

## Operations in ring-like Structures

The addition is named [rngl_add] and the multiplication [rngl_mul].
The opposite and the inverse have three possible states:

- either as a fully defined unary function (e.g. -3, 1/7)
- or undefined but with a partially defined binary function (e.g 5-3, 12/3)
- or undefined

This is represented by [rngl_opt_opp_or_subt] and [rngl_opt_inv_or_quot].
For a type [T], both are of type [option (sum (T → T) (T → T → T))]:

- for a set holding an opposite [opp], we have
<<
    rngl_opt_opp_or_subt := Some (inl opp)
>>
- for a set holding a partial subtraction [subt], we have
<<
    rngl_opt_opp_or_subt := Some (inr subt)
>>
- for a set holding neither opposite, not subtraction, we have
<<
    rngl_opt_opp_or_subt := None
>>

Same for [rngl_opt_inv_or_quot] for inverse and partial division.

There is a syntax, named [%L]:

- we can write [(a+b)%L] instead of [rngl_add a b],
- we can write [(a*b)%L] instead of [rngl_mul a b].

No need to repeat the [%L] for each sub-expression. We can write
[(a+b*c)%L] with one only [%L].

We also have:
<<
  rngl_opp a :=
    | opp a         if rngl_opt_opp_or_subt = Some (inl opp)
    | 0             otherwise
>>
<<
  rngl_inv a :=
    | inv a         if rngl_opt_inv_or_quot = Some (inl inv)
    | 0             otherwise
>>
<<
  rngl_sub a b :=
    | a + opp b     if rngl_opt_opp_or_subt = Some (inl opp)
    | subt a b      if rngl_opt_opp_or_subt = Some (inr subt)
    | 0             otherwise
>>
<<
  rngl_div a b :=
    | a * inv b     if rngl_opt_inv_or_quot = Some (inl inv)
    | quot a b      if rngl_opt_inv_or_quot = Some (inr quot)
    | 0             otherwise
>>

And the syntaxes:

- [(-a)%L] for [rngl_opp a]
- [(a⁻¹)%L] for [rngl_inv a]
- [(a-b)%L] for [rngl_sub a b]
- [(a/b)%L] for [rngl_div a b]

The identity element of addition is [rngl_zero] and can be written [0%L].

The identity element of multiplication is optional. It is named
[rngl_opt_one]. In can be absent in some structures, e.g. ideals,
and we have:
<<
  rngl_one :=
    | one     if rngl_opt_one = Some one
    | 0       if rngl_opt_one = None
>>
and the syntax [1%L] for [rngl_one].

...

(documentation, work in progress)

...

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

## Usage

This file provides the main interface of the RingLike library. It gathers
all the relevant modules, so users only need to:
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
