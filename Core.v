(** * Ring-like structures: overview

This library provides a common interface for algebraic structures that
resemble rings, but may differ by the presence or absence of operations
like subtraction or division.

Each ring-like structure is defined by:

- a type [T],
- a collection of operations (addition, multiplication, zero, one, etc.),
- and two optional fields:
<<
      rngl_opt_opp_or_subt : option (sum (T → T) (T → T → T))
      rngl_opt_inv_or_quot : option (sum (T → T) (T → T → T))
>>

These fields describe whether the structure provides:

- no operation        (None)
- a unary operation   (Some (inl f))  e.g. negation or inverse
- a binary operation  (Some (inr f))  e.g. subtraction or division

Examples:

- Natural numbers ℕ:
<<
      rngl_opt_opp_or_subt = Some (inr Nat.sub)
      rngl_opt_inv_or_quot = Some (inr Nat.div)
>>

- Integers ℤ:
<<
      rngl_opt_opp_or_subt = Some (inl Z.opp)
      rngl_opt_inv_or_quot = Some (inr Z.quot)
>>

- Rationals ℚ:
<<
      rngl_opt_opp_or_subt = Some (inl Qopp)
      rngl_opt_inv_or_quot = Some (inl Qinv)
>>

This representation allows uniform reasoning over semirings, rings, and fields.

For convenience, we define:
<<
      rngl_has_opp := rngl_opt_opp_or_subt = Some (inl _)
      rngl_has_inv := rngl_opt_inv_or_quot = Some (inl _)
>>

Which means:

- Semirings: rngl_has_opp = false, rngl_has_inv = false
- Rings:     rngl_has_opp = true,  rngl_has_inv = false
- Fields:    rngl_has_opp = true,  rngl_has_inv = true
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
