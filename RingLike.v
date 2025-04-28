(* Ring-like *)
(* Algebraic structures with two operations *)
(* Allows to define all kinds of semirings, rings, fields *)
(* Allows to define semirings, rings, fields, commutative or not,
   with two classes:
     ring_like_op, holding the operations, and
     ring_like_prop, holding their properties.
   In class ring_like_prop, we can set,
     to make a semiring:
        rngl_opt_opp_or_subt = Some (inr subt) where subt is a subtraction
        rngl_opt_opp_or_subt = None otherwise
        rngl_opt_inv_or_quot = Some (inr quot) where quot is a quotient
        rngl_opt_inv_or_quot = None otherwise
     to make a ring:
        rngl_opt_opp_or_subt = Some (inl opp), where opp is the opposite
        rngl_opt_inv_or_quot = Some (inr quot) where quot is a quotient
        rngl_opt_inv_or_quot = None otherwise
     to make a field:
        rngl_opt_opp_or_subt = Some (inl opp), where opp is the opposite
        rngl_opt_inv_or_quot = Some (inl inv), where inv is the inverse
   Multiplication can be commutative or not by setting rngl_mul_is_comm
   to true or false.
   There are many other properties that are implemented here or could be
   implemented :
     - archimedean or not
     - with decidable equality or not
     - with commutative multiplication or not
     - with some characteristic
     - finite or infinite
     - ordered or not
     - valuated or not
     - principal or not
     - factorial or not
     - euclidean or not
     - algebraically closed or not
     - complete or not
     - with associative addition or multiplication or not
     - with commutative addition or not
     - with 0 or without, right or left
     - with 1 or without, right or left
     - with specific subtraction (subt) or not
     - with specific division or not
     and so on. *)

Require Export RingLike_structures.
Require Export RingLike_order.
Require Export RingLike_add.
Require Export RingLike_mul.
Require Export RingLike_div.
Require Export RingLike_add_with_order.
Require Export RingLike_mul_with_order.
Require Export RingLike_div_with_order.
Require Export RingLike_distances.
