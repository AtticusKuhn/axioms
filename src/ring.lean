-- import data.set


class has_group_notation (R : Type) extends has_mul R, has_add R, has_zero R, has_one R, has_neg R, has_dvd R, has_sub R
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
  (divs : ∀(a b :R), a ∣ b ↔ (∃ (c:R), a*c=b))
  /- -a is the inverse of a-/
  (add_neg : ∀(a : R), a + -a = 0)
  (subtr : ∀(a b : R), a - b =  a + -b)

  -- (exp : ∀(a : R)( r: ℕ ), a^r = a*a^(r-1))

 
namespace ring
  variables {R : Type} [ring R]
  class ordered_ring (R  : Type) extends ring R, has_lt R, has_le R
  class Integers (ZZ  : Type) extends   ordered_ring ZZ :=
    (WOP : ∀(proposition : ZZ → Prop), 
    ((∃ (some:ZZ), 
    proposition(some)) → (
      ∃(minimal : ZZ), 
      proposition(minimal) ∧  
      ∀(other:ZZ), 
      proposition(other)→ minimal ≤ other
    )))


  variables { O : Type} [ordered_ring O ]
  variables { ZZ : Type} [Integers ZZ ]

  theorem explicit_WOP: ∀(proposition : ZZ → Prop), 
    (∃ (some:ZZ), 
    proposition(some)) → (
      ∃(minimal : ZZ),
      proposition(minimal) ∧  
      ∀(other:ZZ), 
      proposition(other)→ minimal ≤ other
    ) := begin
    exact Integers.WOP,
    end

  /-hacky way to define propositions as a black box -/
  def is_positive : (O) → Prop := begin
    sorry,
  end
  /- The positives are closed under multiplication -/
  axiom pos_times_pos:  ∀{ a b : O}, is_positive a → is_positive b → is_positive (a*b)
  /- The positives are closed under addition -/
  axiom pos_plus_pos:  ∀{ a b : O}, is_positive a → is_positive b → is_positive (a+b)
  /- The trivial ring is not ordered -/
  axiom nontriviality:  ¬ is_positive(0:O)
  /- At leaset one element of the ring is positive -/
  axiom nonempty_pos : ∃{a : O}, is_positive a
  /- One of the following is true: a is positive, a = 0, or -a is positive -/
  axiom trichotomy:  ∀( a : O),
   ( is_positive a ∧ (a ≠ 0) ∧ ¬ is_positive (-a))
   ∨  ( (¬ is_positive a) ∧  (a=0) ∧ (¬ is_positive (-a)))
   ∨   ( ¬ is_positive a ∧ a≠ 0 ∧  is_positive (-a))
  /- a < b iff ∃p positive, such that b = a + p -/
  axiom less_than: ∀{a b : O}, a < b ↔ (∃(P : O), is_positive P ∧ a + P = b) 
  /- a ≤ b iff a < b or a = b -/ 
  axiom less_eq: ∀{a b : O}, a ≤ b ↔ (a < b ∨ a = b)

 def gcd : ZZ → ZZ → ZZ := begin
    sorry,
  end
  axiom gcd_def : ∀( a b c: ZZ), 
  gcd a b=c ↔ c ∣ a ∧ c ∣ b 
  ∧ (∀(d:ZZ), d ∣ a ∧ d ∣  b → d ≤ c)
  export Integers
end ring
export ring