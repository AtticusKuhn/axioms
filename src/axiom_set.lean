import .ring
-- import tactic
open ring
variables {R : Type} [ring R]
variables { ZZ : Type} [integers ZZ ]

--  variable is_positive : ZZ → Prop
/-
P1. Suppose a, z ∈ ℤ. If a+z=a then z=0. So "zero"
  is uniquely defined. Similarly, "one" is uniquely
  defined. 
-/
theorem zero_is_unique: ∀( z : R), (∀ (a : R), a + z = a) → (z = 0)  := begin
  intros z a,
  have x:  z + 0 = z := add_zero z,
  have y:  z + 0 = 0 := begin 
  rw add_comm,
  rw a,
  end, 
  rw ← x,
  rw y,
end

theorem one_is_unique: ∀( o : R), (∀(a : R), a*o = a) → o = 1  := begin
  intros o a,
  have q : o * 1 = o := mul_one o,
  have r : 1 * o = 1 := a 1,
  rw mul_comm at r,
  rw q at r,
  exact r, 
end

/-
P3. Suppose a,b, b' ∈ ℤ. The a+b=a+b' → b=b'
-/
theorem left_cancel: ∀ {a b c : R}, a+b=a+c → b=c := begin
  intros a b c eq,
  rw [ ← add_zero  b],
  cases has_inv a  ,
  rw [←  h,←  add_assoc,add_comm b a,eq,add_comm a c,add_assoc,h,add_zero],
end

theorem right_cancel: ∀ {a b c : R}, b+a=c+a → b=c := begin
  intros a b c eq,
  rw add_comm at eq,
  have : c + a = a+c := begin
    rw add_comm,
  end,
  rw this at eq,
  have : b=c := begin
    exact left_cancel eq,
  end,
  exact this,
end

lemma mul_zero : ∀{a : R}, a * 0 = 0 :=
begin 
  intro a,
  have : a * (1 + 0) = a + 0,
  {
    rw add_zero,
    rw mul_one,
    rw add_zero,
  },
  rw mul_add at this,
  rw mul_one at this,
  exact left_cancel this,
end

/-
P2. Use P1 to deduce that 0 ≠ 1
-/
theorem zero_is_not_one: (0 : R) ≠ 1 := begin
  sorry, --this is false,
  --this is not provable from the ring axioms
end

/-
P2 SALVAGE. Zero is only one in the trivial ring.
-/
theorem zero_is_one_implies_trivial : ((0: R) = 1) → (∀(a : R), a = 0) := 
begin 
  intros h a,
  have q : a * 1 = a := mul_one a,
  rw ← h at q,
  rw mul_zero at q,
  symmetry,
  exact q,
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


theorem neg_neg_a : ∀ {a : R}, -(-a)=a := begin 
  intro a,
  have na := add_neg a,
  have nna := add_neg (-a),
  rw add_comm at nna,
  rw ← na at nna,
  exact right_cancel nna,
end

theorem dist_neg_left : ∀ (a b : R), (a)*(-b)=-(a*b) := begin 
  intros a b,
  have x: 0 = a*0 := begin
  rw mul_zero,
  end,
  rw ← add_neg b at x,
  rw mul_add at x,
  rw add_neg b at x,
  have y: a*b + (-(a*b)) = 0 := begin
  rw add_neg (a*b),
  end,
  rw ←  y at x,
  have := left_cancel x,
  symmetry,
  exact this,
end

theorem mul_neg_one : ∀ (a : R), (-1)*a=-a := begin 
  intro a,
  have x: a*0=0 := begin
  exact mul_zero,
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
  exact left_cancel x,
  end,
  rw mul_comm,
  exact z,
  end

theorem neg1_times_neg1 : (-(1 :R))*(-1) = 1 := begin
  have x: (-1:R)*(0:R)=0 := begin
    exact mul_zero,
  end,
  rw ←  add_neg (1 :R ) at x,
  rw mul_add at x,
  rw mul_one at x,
  rw comm at x,
  have : (-1 :R)* (-1)  = 1 := begin
    rw right_cancel x,
  end,
  exact this,
end

theorem one_pos : ¬ is_positive(-1:ZZ) := begin
  by_contradiction,
  have : is_positive (-(1:ZZ)* -1) := begin
    exact pos_times_pos h h,
  end,
  rw neg1_times_neg1 at this,
  have x : xor ( xor (is_positive (-1:ZZ ) ) (-1= (0 : ZZ)) ) (is_positive (-(-1) :ZZ)) := begin
  exact trichotomy (-1 :ZZ),
  end,
  rw neg_neg_a at x,
  cases x with u p, {
  -- right u,
  cases u with r s,
  apply s,
  exact this,
  },
  cases p with gt rs,
  -- cases rs with am pr,
apply rs,
left,
split,{
  exact h,
},

 sorry,
  -- use this at x,
  -- sorry,
end