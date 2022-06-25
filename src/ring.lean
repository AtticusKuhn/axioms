-- import data.set


class has_group_notation (R : Type) extends has_mul R, has_add R, has_zero R, has_one R, has_neg R
class ring (R : Type) extends has_group_notation R :=
  /- associativity of multiplication-/
  (mul_assoc : ∀ (a b c : R), a * b * c = a * (b * c))
  /- anything times one is just itself-/
  (mul_one : ∀ (a : R), a * 1 = a)
  /- multiplication is commutative-/
  (mul_comm : ∀(a b : R), a * b = b * a)
  /- addition is associative-/
  (add_assoc : ∀(a b c : R), a + b + c = a + (b + c))
  /- anything plus zero is just itself-/
  (add_zero : ∀(a : R), a + 0 = a)
  /- addition is commutative-/
  (add_comm : ∀(a b : R),  a+ b = b+ a)
  /- multiplication distributes over addtion-/
  (mul_add : ∀(a b c : R), a * (b + c) = a * b + a * c)
  /- all numbers have an additive inverse-/
  (has_inv : ∀(a : R), ∃(x : R), a + x = 0)
  /- -a is the inverse of a-/
  (add_neg : ∀(a : R), a + -a = 0)

namespace ring
  variables {R : Type} [ring R]
  class ordered_ring (R  : Type) extends ring R, has_lt R, has_le R
  variables { O : Type} [ordered_ring O ]
  /-hacky way to define propositions as a black box -/
  def is_positive : (O) → Prop := begin
    sorry,
  end
  def Pos_Set: set O := {z : O | is_positive z } 
  axiom pos_times_pos:  ∀{ a b : O}, is_positive a → is_positive b → is_positive (a*b)
  axiom pos_plus_pos:  ∀{ a b : O}, is_positive a → is_positive b → is_positive (a+b)
  axiom nontriviality:  ¬ is_positive(0:O)
  axiom nonempty_pos : ∃{a : O}, is_positive a
  axiom trichotomy:  ∀( a : O),
   ( is_positive a ∧ (¬ a=0) ∧ ¬ is_positive (-a))
   ∨  ( (¬ is_positive a) ∧  (a=0) ∧ (¬ is_positive (-a)))
   ∨   ( ¬ is_positive a ∧ ¬ a=0 ∧  is_positive (-a))
  --  xor ( xor (is_positive a) (a=0) ) (is_positive (-a)) ∧ xor (  (is_positive a)) (xor (a=0)  (is_positive (-a)))
  axiom less_than: ∀{a b : O}, a < b ↔ (∃(P : O), is_positive P ∧ a + P = b)  
  axiom less_eq: ∀{a b : O}, a ≤ b ↔ (a < b ∨ a = b)
end ring
export ring