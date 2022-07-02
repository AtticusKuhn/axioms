import .ring
import .set_1
-- import tactic
open ring
variables {R : Type} [ring R]
variables {O : Type} [ordered_ring O ]
variables {ZZ : Type} [Integers ZZ ]

theorem WOP_Contradiction: 
  ∀ (proposition: ZZ → Prop),
  ( ∀(minimal: ZZ), ∃(smaller: ZZ),
  ¬proposition(minimal) → ¬proposition(smaller) 
  ∧ smaller < minimal ) → (∀ (x : ZZ), 
  proposition(x)) 
  := begin
  intros prop holds_for_smaller all,
  by_contradiction,
  -- let notprop: ∀(x:ZZ), x → Prop := ¬ proposition(x),
  -- let f : ℕ → ℕ := λ n, n + 1,

  have  wop := WOP (λ x, ¬ prop(x)),

  -- cases wop,

  -- have wopp_thing :  (∃ (minimal : ZZ), ∀ (other : ZZ), (λ (x : ZZ), ¬prop x) other → minimal ≤ other) := begin
  --   -- exact wop_h h,
  --   -- intros a,
  --   -- exact wop_h a,
  -- end,

  -- cases wop_h,
  -- have mins := wop_h (h),
  sorry,
end 
theorem pos_is_g0: ∀ (x:O), is_positive x ↔ 0< x := begin
intros a,
split, {
intros pa,
rw less_than,
split,{
split, {
exact pa,
},
rw zero_add,
},
},
intros la,
rw less_than at la,
cases la, {
cases la_h, {
rw zero_add at la_h_right,
rw  la_h_right at la_h_left,
exact la_h_left,
},
},
end


theorem Euclidean_Algorithm_Exists: ∀ (a b: ZZ), ∃ (q r :ZZ), a=b*q+r := begin
intros a b,
split, {
  split, {
    have : a = b*0 + a := begin
    rw mul_zero,
    rw zero_add,
    end,
    exact this,
  },
},
end

def nibzo : ZZ → Prop := λ x, 0<x ∧ x < 1

theorem squares_pos: ∀ (a: O), 0 <a → 0 < a*a := begin
intros a ag0,
rw less_than at ag0,
cases ag0 with p pos,
cases pos with ppos pea,
rw less_than,
have pspos := pos_times_pos ppos ppos,

split, {
split, {
exact pspos,
},
rw zero_add,
rw zero_add at pea,
rw pea,
},

end  

theorem NIBZO: ¬ (∃ (x:ZZ), nibzo(x)) := begin
  -- apply WOP to NIBZO
  have wop_on_nibzo := explicit_WOP  nibzo , {
   --Proof by contradiction, assume NIBZO doesn't hold
  intros contradict,
  -- then there exists a minimum element on which NIBZO doesn't hold
  have has_min := wop_on_nibzo contradict,
  -- call the minimum element min
  cases has_min with  min others,
  -- we have that min satisfies ¬nibzo
  have x : 0 < min ∧ min < 1,{
    cases others with nibzo_min, 
    change (0 < min ∧ min < 1) at nibzo_min,
    exact nibzo_min,
  },
  cases x with x1 x2,
  -- since  0 < min, then 0 < min*min
  have x : 0 < min*min := begin
    exact squares_pos min x1,
  end,
  -- since 0 < min*min, then min*min is positive
  have minpos: is_positive min := begin
    rw ← pos_is_g0 at x1,
    exact x1,
  end,
  -- since min < 1, then min ≤ 1
  have xle1 : min ≤ 1 := begin
    rw less_eq,
    left,
    exact x2,
  end,
  -- since min < 1, then min*min < 1 
  have minmin_lt_1 :  min*min < 1 := begin
    have mmin_le_1 :=  mul_lt_mul (minpos) (minpos) (x2) (x2) ,
    rw mul_one at mmin_le_1,
    exact mmin_le_1,
  end,
  -- since min < 1, then min*min < min
  have smaller: min*min < min := begin
    have minthing := mul_le min 1 min minpos x2 ,
    simp at minthing,
    exact minthing,
  end,
  cases others,
  -- min*min satisfies nibzo
  have nibzominmin : nibzo (min*min) := begin
    change (0 < min*min ∧ min*min < 1),
    split, {
      exact x,
    },
    exact minmin_lt_1
  end,
  -- finally, this is a contradiction because we assumed min was the smallest element
  have min_le_minmin := others_right (min*min) nibzominmin,
  rw less_eq at min_le_minmin,
  cases min_le_minmin, {
    have less_self := trans_lt min_le_minmin smaller,
    apply no_lt_self min,
    exact less_self,
  },
  rw ←  min_le_minmin at smaller,
  apply no_lt_self min,
  exact smaller,
  },
end

theorem push_not_exists: ∀{x : Type}, ∀{p: x→ Prop}, (¬ (∃(q : x), p(q))) ↔ (∀ (q : x), ¬ p(q)):=
begin
sorry,
end
theorem push_and: ∀{p q : Prop}, (¬ (p ∧ q)) ↔ (¬ p ∨ ¬ q):=
begin
sorry,
end
theorem not_le_ge: ∀{a b : O}, (¬ (a < b)) ↔ ( b ≤ a):=
begin
sorry,
end
theorem sub_both_le: ∀(a b x: O), ((a ≤  b)) ↔ ( a-x ≤ b-x):=
begin
sorry,
end
theorem dist_neg_add: ∀(a b: O), -(a+b)  = -a + -b:=
begin
intros a b,
rw ← mul_neg_one (a+b),
rw mul_add,
rw mul_neg_one,
rw mul_neg_one,
end


@[simp]
theorem lt_cancel: ∀(a b c: O), c+a < c+b ↔ a < b:=
begin
sorry,
end
@[simp]
theorem neg_comp: ∀(a b: O), -a < -b ↔ b < a:=
begin
sorry,
end
theorem not_le_iff_ge: ∀(a b: O), a < b ↔ ¬ (b ≤  a):=
begin
sorry,
end


theorem Euclidean_Algorithm_One_Step_two: ∀ (a b: ZZ),  is_positive a → is_positive b → ∃ (q r :ZZ), a=b*q+r ∧ r < b :=
begin
  --introduce variable a b,
  intros a b a_pos b_pos,
  -- defined the set
  let WOP_prop : ZZ → Prop := λ s, ∃ (q : ZZ), s = a-b*q ∧  0 ≤ a-b*q,
  -- perform WOP on the set
  have WOP := explicit_WOP WOP_prop,
  -- WOP holds on a
  have a_WOP_Prop : WOP_prop a := begin
  change (∃ (q : ZZ), a = a-b*q ∧ 0 ≤  a-b*q),
  split, {
    split, {
        have zero_work :a = a - b * 0 := begin
        rw mul_zero,
        rw sub_zero,
        end,
        exact zero_work,
    },
  rw mul_zero,
  rw sub_zero,
  -- 0 < a
  have a_ge_0 : 0 < a := begin
    have a_pos_iff := pos_is_g0 a,
    cases a_pos_iff with forward backward,
    exact forward a_pos,
  end,
  rw less_eq,
  left,
  exact a_ge_0
  },
end,
-- there exists an integer for which the proposition holds
have WOP_some :  (∃ (some : ZZ), WOP_prop some) := begin
split,{
exact a_WOP_Prop,
},
end,
-- the set has a minimal element
have WOP_min := WOP WOP_some,
-- call the minimal element min
cases WOP_min with min min_smallest,
cases min_smallest with WOP_Prop_min min_smaller_other,
change  (∃ (q : ZZ), min = a-b*q ∧ 0 ≤  a-b*q) at WOP_Prop_min,
cases WOP_Prop_min with q q_eq,
cases q_eq with q_eq q_small,
split, {
split, {
split, {
  have thing :a = b * q + min := begin
  rw q_eq,
  rw subtr,
  rw ← add_assoc,
rw add_comm,
rw ←  add_assoc,
rw add_comm (-(b * q)) ((b * q)),
rw add_neg,
rw zero_add,
  end,
  exact thing,
},
-- proof by contradiction, assum min ≥ b
by_contradiction contradict,
rw not_le_ge at contradict,
rw sub_both_le (b) (min) (b) at contradict,
simp at contradict,
-- 0 ≤ a  - b *  (q +1)
have smallerthing : 0 ≤ a  - b *  (q +1) := begin
rw subtr,
rw mul_add,
rw mul_one,
rw dist_neg_add,
rw ← add_assoc,
rw ← subtr,
rw ← subtr,
rw ←  q_eq,
exact contradict,
end,
-- 0 ≤ a  - b *  (q +1) ∈ S
have prop_smaller: WOP_prop (a  - b *  (q +1)) := begin
change  (∃ (x : ZZ), a  - b *  (q +1) = a-b*x ∧ 0 ≤  a-b*x),

split, {
split, {
  have reflx : a - b * (q + 1) = a - b * (q+1), {
refl,
  },
  exact reflx,
},
exact smallerthing,
},
end,
-- a - b * (q + 1) < a-b*q
 have even_smaller :  a - b * (q + 1) < a-b*q := begin
rw subtr,
rw subtr,
rw mul_add,
rw dist_neg_add,
rw lt_cancel,
rw ← add_zero (-(b * q)),
rw  add_assoc,
rw lt_cancel,
rw zero_add,
rw mul_one,
have b_posit : 0 < b, {
  rw ← pos_is_g0 b,
  exact b_pos,
},
rw  ← neg_zero,
rw neg_comp,
exact b_posit,
 end,
 have min_contra := min_smaller_other (a - b * (q + 1)),
 have app_min  := min_contra prop_smaller,
 rw q_eq at app_min,
  have contra_candidate : ¬ (a - b * q ≤ a - b * (q + 1) ), {
    rw ←  not_le_iff_ge,
    exact even_smaller,
  },
  apply contra_candidate,
  exact app_min,
},
},
-- exact q,
end
--  def
theorem BezoutsLemma: ∀ (a b : ZZ), is_positive a → is_positive b → ∃ (x y : ZZ), a*x+b*y = gcd a b := begin
intros a b a_positive b_positive,
  let WOP_prop : ZZ → Prop := λ s, ∃ (x y : ZZ), a*x + b*y = s,
  have WOP := explicit_WOP WOP_prop,
  have WOP_a :  WOP_prop a, {
    change (∃ (x y : ZZ), a*x + b*y = a),
    split, {
      split, {
        have a_works: a * 1 + b * 0 = a , {
          simp,
          rw mul_one,
          rw add_zero,
        },
        exact a_works,
      },
    },
  },
  have Wop_Some: ∃(some: ZZ), WOP_prop some, {
    split, {
      exact WOP_a
    },
  },
  have WOP_exists := WOP Wop_Some,
  cases WOP_exists with min min_smallest, 
  cases min_smallest with WOP_Min others_smaller,
  change (∃ (x' y' : ZZ), a*x' + b*y' = min) at WOP_Min,
  have euclidean_min := Euclidean_Algorithm_One_Step_two a min a_positive,

  sorry,
end