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

  cases wop,

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

theorem bruh: ∀ (a: O), 0 <a → 0 < a*a := begin
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
--  have 
 have wop_on_nibzo := explicit_WOP  nibzo , {
intros contradict,
cases wop_on_nibzo,
cases contradict,
have same : wop_on_nibzo_w = contradict_w := begin
sorry,
 end,
 rw ←  same at contradict_h,
 have has_min := wop_on_nibzo_h contradict_h,
 cases has_min with  min others,
 have x : 0 < min ∧ min < 1,{

    cases others with nibzo_min, 
    change (0 < min ∧ min < 1) at nibzo_min,
    exact nibzo_min,
    -- sorry,
  },
  cases x with x1 x2,
  -- sorry,
  have x : 0 < min*min := begin
    exact bruh min x1,
  end,
  have minpos: is_positive min := begin
  rw ← pos_is_g0 at x1,
  exact x1,
-- exact  pos_is_g0 (x1),
  end,
  have xle1 : min ≤ 1 := begin
  rw less_eq,
  left,
  exact x2,
  end,
   have xother :  min*min < 1 := begin
   sorry,
    -- exact mul_le_mul (minpos) (minpos) (xle1) (xle1) ,
  end,
  have smaller: min*min < min := begin
   have minthing := mul_le min 1 min minpos x2 ,
  --  rw ← mul_comm at minthing,
   simp at minthing,
   exact minthing,
  --  rw mul_one at brere,
  end,
  cases others,
  have nibzominmin : nibzo (min*min) := begin
    change (0 < min*min ∧ min*min < 1),
    split, {
exact x,
    },
    exact xother
  end,
  have asdasd := others_right (min*min) nibzominmin,
rw less_eq at asdasd,
cases asdasd, {
--  have qwerqe := trichotomy_lt (min) (min*min),
sorry,
},
rw ←  asdasd at smaller,



-- have :=  wop_on_nibzo_h contradict_h,

-- rw wop_on_nibzo at contradict,
-- have := wop_on_nibzo contradict,
--    cases this, {
-- cases h, {
--   have x : this_w = h_w := begin
--   end,
-- have x  := this_h h_h,
-- },
--    },
--  have x := this h,

sorry,
 },

 sorry,
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