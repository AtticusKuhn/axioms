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
  (comm : ∀(a b : R),  a+ b = b+ a)
  /- multiplication distributes over addtion-/
  (mul_add : ∀(a b c : R), a * (b + c) = a * b + a * c)
  /- all numbers have an additive inverse-/
  (has_inv : ∀(a : R), ∃(x : R), a + x = 0)
  /- -a is the inverse of a-/
  (add_neg : ∀(a : R), a + -a = 0)

namespace ring
  variables {R : Type} [ring R]
  class integers ( R  : Type) extends ring R -- :=
  variables { ZZ : Type} [integers ZZ ]
  def is_positive : (ZZ) → Prop := begin
    sorry,
  end
  axiom pos_times_pos:  ∀{ a b : ZZ}, is_positive a → is_positive b → is_positive (a*b)
  axiom pos_plus_pos:  ∀( a b : ZZ), is_positive a → is_positive b → is_positive (a+b)
  axiom nontriviality:  ¬ is_positive(0:ZZ)
  axiom trichotomy:  ∀( a : ZZ), xor ( xor (is_positive a) (a=0) ) (is_positive (-a))
end ring
export ring