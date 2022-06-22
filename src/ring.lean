class has_group_notation (R : Type) extends has_mul R, has_add R, has_zero R, has_one R, has_neg R
class ring (R : Type) extends has_group_notation R :=
  (mul_assoc : ∀ (a b c : R), a * b * c = a * (b * c))
  (mul_one : ∀ (a : R), a * 1 = a)
  (mul_comm : ∀(a b : R), a * b = b * a)
  (add_assoc : ∀(a b c : R), a + b + c = a + (b + c))
  (add_zero : ∀(a : R), a + 0 = a)
  (comm : ∀(a b : R),  a+ b = b+ a)
  (mul_add : ∀(a b c : R), a * (b + c) = a * b + a * c)
  (has_inv : ∀(a : R), ∃(x : R), a + x = 0)
  (add_neg : ∀(a : R), a + -a = 0)

namespace ring
variables {R : Type} [ring R]
end ring
export ring