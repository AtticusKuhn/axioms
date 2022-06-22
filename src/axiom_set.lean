import .ring
-- import tactic
-- open ring
variables {R : Type} [ring R]
/-
P1. Suppor a, z ∈ ℤ. If a+z=a then z=0. So "zero"
  is uniquely defined. Similarly, "one" is uniquely
  defined. 
-/
theorem zero_is_unique: ∀( z : R), (∀ (a : R), a + z = a) → (z = 0)  := begin
  intros z a,
  have x:  z + 0 = z := begin 
  rw add_zero,
  end, 
 have y:  z + 0 = 0 := begin 
 rw comm,
 rw a,
  end, 
  rw ← x,
  rw y,
end

theorem one_is_unique: ∀( o : R), ∀ (a : R), a*o = a → o = 0  := begin
sorry,
end

/-
P2. Use P1 to deduce that 0 ≠ 1
-/
theorem zero_is_not_one: 0 ≠ 1 := begin

sorry,
end

/-
P3. Suppose a,b, b' ∈ ℤ. The a+b=a+b' → b=b'
-/
theorem left_cancel: ∀ (a b c : R), a+b=a+c → b=c := begin
intros a b c eq,
rw [ ← add_zero  b],
cases has_inv a  ,
rw [←  h,←  add_assoc,comm b a,eq,comm a c,add_assoc,h,add_zero],
end

/-
P4. Gvien a ∈ ℤ, let -a be the unique solution 
x to a+x=0 (why is it unique?)
Then : -(-a)  = a and
-(ab)=(-a)b = a(-b).
Moreover (-a)(-b) = ab 
and
-a = (-1)*a
-/
lemma mul_zero : ∀ (a : R), a*0 = 0 := begin
intros a,
have x: a*(1+0) = a*1 := begin
rw add_zero,
end,
rw mul_add at x,
rw ←  add_zero (a*1) at x,
have y: 0 + a*0 = 0 := begin
rw left_cancel (a*1) (0+a*0) 0,
rw ←  add_assoc,
exact x,
end,
rw comm  0(a*0) at y,
rw add_zero at y,
exact y
end

theorem neg_neg_a : ∀ (a : R), -(-a)=a := begin 
sorry,
end
theorem mul_neg_one : ∀ (a : R), (-1)*a=-a := begin 
intro a,
have x: a*0=0 := begin
exact mul_zero a,
end,
rw ←  add_neg (1:R) at x,
rw mul_add at x,
rw mul_one at x,
rw add_neg at x,
have z: a + -a = 0 := begin
rw add_neg,
end,
rw ← z at x,
have z : a*(-1) = -a := begin

rw  left_cancel (a) (a*(-1) ) (-a) at x,

-- exact x,
sorry,
sorry,
end,
sorry,
end