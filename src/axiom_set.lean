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
  rw add_comm at x,
  have : (-1 :R)* (-1)  = 1 := begin
    rw right_cancel x,
  end,
  exact this,
end
theorem pos_diff : ∀ (a b : ZZ), is_positive (a) ∧ ¬ is_positive (b) → ¬ a=b :=
begin
intros a b c,
cases c with d e,
by_contradiction,
rw h at d,
apply e,
exact d,
-- sorry,
end
theorem pos_not_z : ∀ (a : ZZ), is_positive (a) → ¬ a=0 :=
begin
  intros a b c,
  have nontriv := nontriviality,
  apply nontriv,
  rw c at b,
  exact b,
end

theorem not_neg_one_pos : ¬ is_positive(-1:ZZ) := begin
  intros a,
  have notz := pos_not_z (-1:ZZ),
  have xf := notz a,
  have trich := trichotomy (-1:ZZ),
  have ewf := pos_times_pos a a,
  rw neg1_times_neg1 at ewf,
  cases trich with f g, {
    cases f with d n, 
    cases n with d s,
    rw neg_neg_a at s,
    apply s,
  exact ewf,
  },
  cases g with fn dw,{
    cases fn with dj dw,
    cases dw with dn fh,
    rw neg_neg_a at fh,
    apply fh,
    exact ewf,
  -- sorry,
},
cases dw with fs wh,
cases wh with od wx,
apply fs,
exact a,
end
theorem one_pos : is_positive(1:ZZ) := begin
  have ed : ¬is_positive(-1:ZZ) := not_neg_one_pos,
  cases trichotomy (1:ZZ),
  {
    cases h with h1 h2,
    exact h1,
  },
  {
    cases h,
    cases h with h1 h2,
    cases h2 with h2 h3,
    have h4 : 0 = (1 : ZZ),
    {
      symmetry,
      exact h2,
    },
    {
      have allzero := zero_is_one_implies_trivial h4,
      have zeronotpos : ∃(a : ZZ), is_positive a := nonempty_pos,
      rw h2 at h1,
      cases zeronotpos with a q,
      have azero := allzero a,
      rw ← h2 at azero,
      rw azero at q,
      exact q,
    },
    {
      cases h with h1 h2,
      cases h2 with h2 h3,
      exfalso,
      apply ed,
      exact h3,
    },
  }
end
