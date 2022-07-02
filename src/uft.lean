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

theorem Contra_Euclidean_Algorithm_One_Step:∃ (a b: ZZ), ¬ ( ∀ (q r :ZZ), (a=b*q+r)→  r > b) := begin
let euclidean : ZZ → Prop := λ a, ∀ (b:ZZ), ¬∀ (  q r : ZZ), a = b * q + r →  r > b,
have := WOP_Contradiction (euclidean) ,
have thing :(∀ (minimal : ZZ), ∃ (smaller : ZZ), ¬euclidean minimal → ¬euclidean smaller ∧ smaller < minimal)  := begin
intros minimal,
split, {
  intros em,
  -- change (¬euclidean minimal) with (∀ (a b q r :ZZ), (a=b*q+r)→  r > b) at  em,
  -- rw euclidean at em,
sorry,
},
sorry,
end,
 have that := this thing,
 sorry,
-- exact that,

end
theorem Euclidean_Algorithm_One_Step_two: ∀ (a b: ZZ), ∃ (q r :ZZ), a=b*q+r ∧ r < b :=
begin
intros a b,
let WOP_prop : ZZ → Prop := λ s, ∃ (q : ZZ), s = a-b*q ∧ a-b*q > 0,
have WOP := explicit_WOP WOP_prop,
cases WOP,

sorry,
end
--  def
theorem Euclidean_Algorithm_One_Step: ∀ (a b: ZZ), ∃ (q r :ZZ), a=b*q+r ∧ r < b := begin
-- intros a b,
let euclidean : ZZ → Prop := λ a, ∀ ( b: ZZ), ∃ (q r :ZZ), a=b*q+r ∧ r < b,
have := WOP_Contradiction (euclidean) ,
have thing : (∀ (minimal : ZZ), ∃ (smaller : ZZ), ¬euclidean minimal → ¬euclidean smaller ∧ smaller < minimal)  := begin 
intros a,
split, {
intros na,

-- rw euclidean,
sorry,
},
exact a,
-- sorry,
end,
have that := this thing,
exact that,
-- cases this,
-- sorry,
end