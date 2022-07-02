import .ring
-- import tactic
open ring
variables {R : Type} [ring R]
variables {O : Type} [ordered_ring O ]

--  variable is_positive : O → Prop
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

/- similarly, you can cancel on the right-/
-- @[simp]
lemma right_cancel: ∀ {a b c : R}, b+a=c+a → b=c := begin
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

/- anything times zero is zero -/

@[simp]
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
False. 0 = 1 in the trivial ring.`
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
@[simp]
theorem neg_neg_a : ∀ {a : R}, -(-a)=a := begin 
  intro a,
  have na := add_neg a,
  have nna := add_neg (-a),
  rw add_comm at nna,
  rw ← na at nna,
  exact right_cancel nna,
end

@[simp]
theorem dist_neg_right : ∀ (a b : R), (a)*(-b)=-(a*b) := begin 
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

@[simp]
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
@[simp]
theorem dist_neg_left : ∀ (a b : R), (-a)*(b)=-(a*b) := begin 
  intros a b,
  rw ← mul_neg_one a,
  rw mul_comm (-1:R) a,
  rw mul_assoc,
  rw  mul_neg_one b,
  exact dist_neg_right a b,
end
@[simp]
theorem dist_neg_both : ∀ (a b : R), (-a)*(-b)=(a*b) := begin 
  intros a b,
  rw dist_neg_left (a) (-b),
  rw dist_neg_right (a) (b),
  rw neg_neg_a,
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
/-
  P7
  1 ∈ P and -1 ∉ P
-/

/-
  lemma: if a is positive and b is not positive then a is not b
-/
lemma pos_diff : ∀ (a b : O), is_positive (a) ∧ ¬ is_positive (b) → ¬ a=b :=
begin
  intros a b c,
  cases c with d e,
  by_contradiction,
  rw h at d,
  apply e,
  exact d,
end
/-
  lemma: if a is positive then a is not 0
-/
lemma pos_not_z : ∀ (a : O), is_positive (a) → ¬ a=0 :=
begin
  intros a b c,
  have nontriv := nontriviality,
  apply nontriv,
  rw c at b,
  exact b,
end

/-
  -1 ∉ P : in other words, -1 is not positive 
-/
theorem not_neg_one_pos : ¬ is_positive(-1:O) := begin
  intros a,
  have notz := pos_not_z (-1:O),
  have xf := notz a,
  have trich := trichotomy (-1:O),
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
  },
  cases dw with fs wh,
  cases wh with od wx,
  apply fs,
  exact a,
end
/-
  1 ∈ P : in other words 1 is positive
-/
theorem one_pos : is_positive(1:O) := begin
  have ed : ¬is_positive(-1:O) := not_neg_one_pos,
  cases trichotomy (1:O),
  {
    cases h with h1 h2,
    exact h1,
  },
  {
    cases h,
    cases h with h1 h2,
    cases h2 with h2 h3,
    have h4 : 0 = (1 : O),
    {
      symmetry,
      exact h2,
    },
    {
      have allzero := zero_is_one_implies_trivial h4,
      have zeronotpos : ∃(a : O), is_positive a := nonempty_pos,
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

theorem trans_lt : ∀{a b c : O}, a < b → b <  c → a < c := begin
sorry,
end
/-
  P8 Prove the transitivity of ≤ 
-/
theorem trans_le : ∀{a b c : O}, a ≤ b → b ≤ c → a ≤ c :=
begin 
  intros a b c ab bc,
  rw less_eq at ab,
  rw less_eq at bc,
  rw less_eq,
  cases ab,
  {
    cases bc,
    {
      rw less_than at ab,
      rw less_than at bc,
      cases bc with Pbc bc,
      cases ab with Pab ab,
      cases bc with Pbc bc,
      cases ab with Pab ab,
      rw ← ab at bc,
      rw add_assoc at bc,
      have := pos_plus_pos Pab Pbc,
      have alc : a < c,
      {
        rw less_than,
        split,
        exact ⟨this, bc⟩,
      },
      left,
      exact alc,
    },
    {
      left,
      rw ← bc,
      exact ab,
    },
  },
  {
    cases bc,
    {
      left,
      rw ab,
      exact bc,
    },
    {
      right,
      rw ab,
      exact bc,
    }
  },
end
@[simp]
/- 0 + something = something -/
lemma zero_add : ∀{a : R}, 0 + a = a :=
begin 
  intro a,
  rw add_comm,
  rw add_zero,
end
/- move stuff across the equal sign-/
lemma move : ∀{a b c: R}, a + b = c → a = c + (-b) :=
begin 
  intros a b c h,
  rw ← h,
  rw add_assoc,
  rw add_neg,
  rw add_zero,
end
/- you can multiply by stuff on the right-/
lemma mul_right : ∀{a b : R}, ∀(c : R), a = b → a * c = b * c :=
begin 
  intros a b c h,
  rw h,
end

/-
  P9 ∀a, b ∈ ℤ, exactly one of the following is true: a < b or a = b or a > b
  in other words, the integers are a total order.
-/
theorem trichotomy_lt : ∀(a b : O), 
  (a < b ∧ a ≠ b ∧ ¬(b < a)) ∨ 
  (¬(a < b) ∧ a = b ∧ ¬(b < a)) ∨
  (¬(a < b) ∧ a ≠ b ∧ (b < a)) :=
begin 
  intros a b,
  have : a + (b + (-a)) = b,
  {
    rw add_comm,
    rw add_assoc,
    rw add_comm (-a) a,
    rw add_neg,
    rw add_zero,
  },
  cases trichotomy (b + (-a)),
  {
    cases h with h1 h2,
    cases h2 with h2 h3,
    left,
    split,
    {
      rw less_than,
      split,
      exact ⟨h1, this⟩,
    },
    split,
    {
      by_contra,
      rw h at h1,
      rw add_neg at h1,
      exact nontriviality h1,
    },
    {
      by_contra,
      rw less_than at h,
      cases h with P h,
      cases h with h4 h5,
      rw ← this at h5,
      rw ← add_zero a at h5,
      rw add_assoc a 0 at h5,
      rw zero_add at h5,
      rw add_assoc at h5,
      have q := left_cancel h5,
      rw add_zero at q, 
      rw add_comm at q,
      have q2 := move q,
      rw zero_add at q2,
      rw q2 at h4,
      apply h3,
      exact h4,
    },
  },
  cases h,
  {
    right,
    left,
    cases h with h1 h2,
    cases h2 with h2 h3,
    have h4 := move h2,
    rw neg_neg_a at h4,
    rw zero_add at h4,
    split,
    {
      by_contra,
      rw less_than at h,
      cases h with P h,
      cases h with h5 h6,
      rw h4 at h6,
      rw ← add_zero a at h6,
      rw add_assoc at h6,
      have q := left_cancel h6,
      rw zero_add at q,
      rw q at h5,
      exact nontriviality h5,
    },
    split,
    {
      symmetry,
      exact h4,
    },
    {
      by_contra,
      rw less_than at h,
      cases h with P h,
      cases h with h5 h6,
      rw h4 at h6,
      rw ← add_zero a at h6,
      rw add_assoc at h6,
      have q := left_cancel h6,
      rw zero_add at q,
      rw q at h5,
      exact nontriviality h5,
    },
  },
  {
    right,
    right,
    cases h with h1 h2,
    cases h2 with h2 h3,
    split,
    {
      by_contra,
      rw less_than at h,
      cases h with P h4,
      cases h4 with h4 h5,
      rw ← this at h5,
      have q := left_cancel h5,
      rw ← q at h1,
      apply h1,
      exact h4,
    },
    split,
    {
      by_contra,
      apply h2,
      rw h,
      rw add_neg,
    },
    {
      rw less_than,
      have that := move this,
      split,
      split,
      exact h3,
      symmetry,
      exact that,
    },
  },
end
/-
  P10
  ∀a, b, x, y ∈ ℤ, a ≤ b and x ≤ y → a + x ≤ b + y
  and SALVAGE a ≤ b and x ≤ y and a, x ∈ P implies a * x ≤ b * y
-/
theorem add_le_add: ∀{a b x y : O}, a ≤ b → x ≤ y → a + x ≤ b + y :=
begin 
  intros a b x y ab xy,
  rw less_eq,
  rw less_eq at ab,
  rw less_eq at xy,
  rw less_than at ab,
  rw less_than at xy,
  rw less_than,
  cases ab,
  {
    cases xy,
    {
      left,
      cases ab with P1 ab,
      cases xy with P2 xy,
      cases ab with P1pos ab,
      cases xy with P2pos xy,
      have : a + x + (P1 + P2) = b + y,
      {
        rw add_assoc,
        rw ← add_assoc x,
        rw add_comm x,
        rw add_assoc,
        rw xy,
        rw ← add_assoc,
        rw ab,
      },
      have that := pos_plus_pos P1pos P2pos,
      split,
      split,
      exact that,
      exact this,
    },
    {
      left,
      cases ab with P ab,
      cases ab with Ppos ab,
      split,
      split,
      exact Ppos,
      rw xy,
      rw add_assoc,
      rw add_comm y,
      rw ← add_assoc,
      rw ab,
    },
  },
  {
    cases xy,
    {
      left,
      cases xy with P xy,
      cases xy with Ppos xy,
      split,
      split,
      exact Ppos,
      rw add_assoc,
      rw xy,
      rw ab,
    },
    {
      right,
      rw xy,
      rw ab,
    },
  },
end
@[simp]
theorem one_mul: ∀ (a :R), 1*a=a := begin
intro a,
rw mul_comm,
exact mul_one a,
end
theorem no_lt_self: ∀ (a:O), ¬  (a  <a) := begin
intros a b,
rw less_than at b,
cases b, 
cases b_h,
rw ← add_zero (a)  at b_h_right,
rw add_assoc at b_h_right,
have := left_cancel b_h_right,
rw zero_add at this,
rw this at b_h_left,
have := nontriviality,
apply this,
exact b_h_left,
end
theorem mul_le :∀ (a b c :O), is_positive c → a < b → a*c < b*c := begin
intros a b c pc alb ,
rw less_than,
rw less_than at alb,
cases alb, 
 cases alb_h,
  have := mul_right c alb_h_right,
    rw mul_comm at this,
    rw mul_add at this,

split, {
  split, {

--  cases alb_h,

--   
--     -- split, {
      exact pos_times_pos pc alb_h_left,
--     -- },
-- sorry,
  },
  rw mul_comm at this,
  exact this,
  --  cases alb_h,


 
},
-- sorry,
end 
theorem mul_le_mul : ∀{a b x y : O}, is_positive a → is_positive x → a ≤ b → x ≤ y → a * x ≤ b * y :=
begin 
  intros a b x y ap xp ab xy,
  rw less_eq,
  rw less_eq at ab,
  rw less_eq at xy,
  rw less_than at ab,
  rw less_than at xy,
  rw less_than,
  cases ab,
  {
    cases xy,
    {
      left,
      cases ab with P1 ab,
      cases xy with P2 xy,
      cases ab with P1pos ab,
      cases xy with P2pos xy,
      have : x*a + x*P1+ (P2*a + P2*P1) = b*y,
      {
        rw ← ab,
        rw ← xy,
        rw mul_add,
        rw mul_comm (a + P1) x,
        rw mul_add,
        rw mul_comm (a + P1) P2,
        rw mul_add,
      },
      have pp: is_positive (x*P1+ (P2*a + P2*P1)),
      {
        have q := pos_times_pos P2pos P1pos,
        have q2 := pos_times_pos P2pos ap,
        have q3 := pos_times_pos xp P1pos,
        have q4 := pos_plus_pos q2 q,
        exact pos_plus_pos q3 q4,
      },
      split,
      split,
      exact pp,
      rw ← add_assoc,
      rw mul_comm a x,
      exact this,
    },
    {
      left,
      cases ab with P ab,
      cases ab with Ppos ab,
      have := mul_right x ab,
      rw mul_comm at this,
      rw mul_add at this,
      have xppos := pos_times_pos xp Ppos,
      split,
      split,
      exact xppos,
      rw xy,
      rw xy at this,
      rw mul_comm,
      exact this,
    },
  },
  {
    cases xy,
    {
      left,
      cases xy with P xy,
      cases xy with Ppos xy,
      have := mul_right a xy,
      rw mul_comm at this,
      rw mul_add at this,
      have appos := pos_times_pos ap Ppos,
      split,
      split,
      exact appos,
      rw ← ab,
      rw mul_comm a y,
      exact this,
    },
    {
      right,
      rw ab,
      rw xy,
    },
  },
end 

theorem le_all: ∀(a :O), a ≤ a := begin
intro a,
rw less_eq,
right,
refl,
end
theorem mul_lt_mul : ∀{a b x y : O}, 
  is_positive a → 
  is_positive x → 
  a < b → 
  x < y → 
  a * x < b * y :=
begin
 sorry,
end

/- If a is positive then it isn't zero -/
lemma pos_not_zero: ∀ {a : O}, is_positive a → a ≠ 0 := begin
  intros a b,
  by_contradiction,
  rw h at b,
  have := nontriviality,
  apply this,
  exact b,
end
/- modus tollens + demorgans law-/
lemma thing : ∀ {P Q R : Prop}, (¬ P ∧  ¬ Q → ¬ R) → (R →  P ∨  Q) := begin 
  intros P Q R pqr r,
  by_cases P, --classical logic
  left,
  exact h,
  by_cases Q,
  right,
  exact h,
  have : ¬P ∧ ¬Q,
  split ; assumption,
  have that := pqr this,
  exfalso,
  apply that,
  exact r,
end
@[simp]
/- -0 = 0-/
lemma neg_zero : -(0 : R) = 0 := 
begin 
  rw ← mul_neg_one,
  rw mul_zero,
end
@[simp] lemma sub_zero: ∀{a:R}, a-0=a := begin
intros a,
rw subtr a (0:R),
rw neg_zero,
rw add_zero,
end
@[simp] lemma sub_self: ∀{a:R}, a-a=0 := begin
intros a,
rw subtr a (a),
exact add_neg a,
end
/- 

  P6: SALVAGE: In an ordered ring:  ab = 0 → a = 0 or b = 0
  we proved the contrapositive because it was easier and a constructive proof
  the lemma "thing" was used to recover the original version
-/
lemma zero_or' : ∀(a b : O),   a ≠ 0 ∧  b ≠ 0 → a *b ≠  (0:O) :=
begin
  intros a b c,
  cases c with d e,
  have ta := trichotomy a,
  have tb := trichotomy b,
  cases ta with s f, {
    cases tb with d g, {
      cases s with asd fsa, 
      cases d with sdd asd,
      cases asd with fds awe,
      cases fsa with sdad qwe,
      exact pos_not_zero (pos_times_pos asd sdd),
    },
    cases s with asd fdj,
    cases g with daskd weq, {
      cases daskd with das qwem,
      cases fdj with as xz,
      cases qwem with oasd we,
      exfalso,
      rw oasd at e,
      apply e,
      refl,
    },
    {
      cases fdj with asds wqer,
      cases weq with asdd tewoirm,
      cases tewoirm with  gfs qowi,
      have := pos_not_zero (pos_times_pos asd qowi),
      rw dist_neg_right at this,
      intro h,
      apply this,
      have that := mul_right (-1 : O) h,
      rw mul_comm at that,
      rw mul_neg_one at that,
      rw mul_comm (0 : O) (-1) at that,
      rw mul_zero at that,
      exact that,
    },
  },
  {
    cases f with w q,
    {
      cases w with junk w,
      cases w with w junk2,
      exfalso,
      apply d,
      exact w,
    },
    {
      cases tb with tb1 tb2,
      {
        cases q with junk q,
        cases q with junk2 negapos,
        cases tb1 with bpos junk3,
        have := pos_not_zero (pos_times_pos negapos bpos),
        intro h,
        apply this,
        rw dist_neg_left,
        rw h,
        simp,
      },
      cases tb2 with tb2 tb3,
      {
        cases tb2 with junk3 tb2,
        cases tb2 with tb2 junk4,
        exfalso,
        apply e,
        exact tb2,
      },
      {
        cases q with junk q,
        cases q with junk2 negapos,
        cases tb3 with junk3 tb3,
        cases tb3 with junk4 negbpos,
        have := pos_not_zero (pos_times_pos negapos negbpos),
        rw dist_neg_both at this,
        exact this, 
      },
    },
  },
end
/- The actually useful version of the lemma -/
lemma zero_or : ∀{a b : O},  a *b= (0:O) → a=0 ∨ b=0:=
begin 
  intros a b,
  have  x1:= zero_or' a b,
  have  x2 := thing x1,
  exact x2,
end
/-
  P6: SALVAGE : In an ordered ring you can cancel multiplication,
  in other words: if c ≠ 0 and a * c = b * c, then a = b
-/
theorem mul_cancel : ∀{a b c : O},  a * c = b * c  → c ≠ 0 → a = b:=
begin 
  intros a b c d cnotzero,
  have start : a * 0 = 0 := by exact mul_zero,
  rw ← add_neg c at start,
  rw mul_add at start,
  rw d at start,
  rw add_neg at start,
  rw dist_neg_right at start,
  rw ← dist_neg_left at start,
  rw mul_comm at start,
  rw mul_comm (-a) c at start,
  rw ← mul_add at start,
  have := zero_or start,
  cases this, {
    exfalso,
    apply cnotzero,
    exact this,
  },
  {
    have that := move this,
    simp at that,
    symmetry,
    exact that,
  }
end
theorem pos_div_pos: ∀ (a b p: O ), is_positive a  → is_positive b → a*p=b → is_positive p := begin
intros a b p a_pos b_pos equ,
-- rw divs at a_divs_b,
-- cases a_divs_b with p equ,
have p_pos : is_positive p, {
by_contradiction,
have trich := trichotomy p,
cases trich, {
cases trich,{
apply h,
exact trich_left,
},

},
cases trich, {
cases trich, {
cases  trich_right, {
rw trich_right_left at equ,
rw mul_zero at equ,
have x:=pos_not_zero b_pos,
apply x,
symmetry,
exact equ,
},
},
},
cases trich,{
cases trich_right,{
have pp := pos_times_pos a_pos trich_right_right,
rw dist_neg_right at pp,
rw equ at pp,
have trichb := trichotomy b,
cases trichb, {
cases trichb, {
cases trichb_right, {
apply trichb_right_right,
exact pp,
},
},
},
cases trichb, {
cases trichb, {
apply trichb_left,
exact b_pos,
},
},
cases trichb ,{
apply trichb_left,
exact b_pos,
},
},
},
},
exact p_pos,
end
/- P5: Subtraction is associative: WRONG and UNSALVAGEABLE -/