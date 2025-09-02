(** * Core

This library is designed to support semirings, rings, fields, and, in
general, algebraic structures containing addition and multiplication and,
optionally, opposite and inverse. For example, it can represent:

- ℕ, ℤ, ℚ, ℝ, ℂ
- ℤ/nℤ
- polynomials
- square matrices
- ideals

Such a general structure is here called a "ring-like".

## SUBTRACTION AND DIVISION

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

## OPERATIONS IN RING-LIKE STRUCTURES

The addition is named [rngl_add] and the multiplication [rngl_mul].
The opposite and the inverse have three possible states:

- either as a fully defined unary function (e.g. -3, 1/7)
- or undefined but with a partially defined binary function (e.g 5-3, 12/3)
- or undefined

This is represented by [rngl_opt_opp_or_psub] and [rngl_opt_inv_or_pdiv].
For a type [T], both are of type [option (sum (T → T) (T → T → T))]:

- for a set holding an opposite [opp], we have
<<
    rngl_opt_opp_or_psub := Some (inl opp)
>>
- for a set holding a partial subtraction [psub], we have
<<
    rngl_opt_opp_or_psub := Some (inr psub)
>>
- for a set holding neither opposite, not subtraction, we have
<<
    rngl_opt_opp_or_psub := None
>>

Same for [rngl_opt_inv_or_pdiv] for inverse and partial division.

There is a syntax, named [%L]:

- we can write [(a+b)%L] instead of [rngl_add a b],
- we can write [(a*b)%L] instead of [rngl_mul a b].

No need to repeat the [%L] for each sub-expression. We can write
[(a+b*c)%L] with one only [%L].

We also have:
<<
  rngl_opp a :=
    | opp a         if rngl_opt_opp_or_psub = Some (inl opp)
    | 0             otherwise
>>
<<
  rngl_inv a :=
    | inv a         if rngl_opt_inv_or_pdiv = Some (inl inv)
    | 0             otherwise
>>
<<
  rngl_sub a b :=
    | a + opp b     if rngl_opt_opp_or_psub = Some (inl opp)
    | psub a b      if rngl_opt_opp_or_psub = Some (inr psub)
    | 0             otherwise
>>
<<
  rngl_div a b :=
    | a * inv b     if rngl_opt_inv_or_pdiv = Some (inl inv)
    | pdiv a b      if rngl_opt_inv_or_pdiv = Some (inr pdiv)
    | 0             otherwise
>>

And the syntaxes:

- [(-a)%L] for [rngl_opp a]
- [(a⁻¹)%L] for [rngl_inv a]
- [(a-b)%L] for [rngl_sub a b]
- [(a/b)%L] for [rngl_div a b]

## IDENTITY ELEMENTS

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

## AND SO ON...

Numerous other definitions, notations and theorems are given in the
sources. Look at their documentation for further information.

There are actually three structures. The first one is named [ring_like_op]
holding the main definitions of functions. The second one is named
[ring_like_ord] for structures having an order relation. The third
one is named [ring_like_prop] holding the axioms required for the
given ring-like, sometimes conditionned by booleans.

For example, this third structure holds a boolean named [rngl_mul_is_comm]
<<
    rngl_mul_is_comm : bool;
>>
specifying that the multiplication is commutative or not. Further, another
field, named [rngl_opt_mul_comm] defines this property which is applied
only if [rngl_mul_is_comm] is [true]:
<<
    rngl_opt_mul_comm :
      if rngl_mul_is_comm then ∀ a b, (a * b = b * a)%L else not_applicable;
>>

## SIMPLE EXAMPLE

This is a elementary code of few lines expressing how to use this library.
It defines a theorem telling that the square of [-1] is [1]. Explanations
follow.
<<
    From Stdlib Require Import Utf8.
    Require Import RingLike.Core.

    Theorem rngl_squ_opp_1 :
      ∀ T (ro : ring_like_op T) (rp : ring_like_prop T),
      rngl_has_1 T = true →
      rngl_has_opp T = true →
      (-1 * -1)%L = 1%L.
    Proof.
    intros T ro rp Hon Hop.
    rewrite (rngl_mul_opp_opp Hop).
    apply (rngl_mul_1_l Hon).
    Qed.
>>

The first line tells that we use utf-8, allowing to write "∀" instead
of "forall", and "→" instead of "->". Using utf-8 is not required to use
RingLike, but the code of this library uses it everywhere.

The second says that we use RingLike. The module [RingLike.Core] includes
 all its main definitions and theorems.

This theorem applies to any type [T] where [1] is defined
([rngl_has_1 = true]) and the opposite exists ([rngl_has_opp T = true]).
This second condition shows that it cannot be applied for example to
the ℕ algebra, since ℕ as no opposite. But it can be used for the algebras
of ℤ, ℝ, polynomials, square matrices, and so on.

## MATHEMATICAL PROPERTIES OF SUBTRACTION

1/ Absorbing element.

In standard mathematics, [0] is an absorbing element for multiplication
(i.e., [∀ a, a × 0 = 0]). This property can be proved in rings and fields,
but not in general semirings, where it must be given as an additional axiom.

However, when a semiring has a subtraction with the property we said above:
<<
      ∀ a b, a + b - b = a      (1)
>>
it is possible to prove it. In that case, the absorbing property need not
be an axiom, it becomes a theorem.

First, we consider the following corollary of (1):
<<
      ∀ a, a - a = 0            (2)
>>

The proof is then the following:
<<
    a*0 = a*0 + a*0 - a*0   by reverse applying (1)
        = a*(0+0) - a*0     by reverse distributivity
        = a*0 - a*0         by property of 0
        = 0                 by applying (2)
>>

In Rocq library, this is proven for the type [nat] by induction. But a
general semiring is not necessarily defined by induction.

2/ Simplification of addition.

A second property that can be proven, when the subtraction exists, is the
simplification of addition:
<<
    ∀ a b c, a + c = b + c → a = b
>>

In semirings, that cannot be proved because we need to add [-c] in the
initial expression, but semirings don't have opposite.

But if the semiring has a subtraction, it can be proven. Knowing that
<< a + c = b + c >> and starting from:
<<
    b + c - c = b
>>
we get
<<
    a + c - c = b
    → a = b
>>

The same way, in Rocq library, this is proven for the type [nat] by
induction, but it is not available in all semirings.
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
