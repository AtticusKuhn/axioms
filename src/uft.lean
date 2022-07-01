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

theorem Contra_Euclidean_Algorithm_One_Step:∃ (a b: ZZ), ¬ ( ∀ (q r :ZZ), (a=b*q+r)→  r > b) := begin
let euclidean : ZZ → Prop := λ a, ∀ (b:ZZ), ¬∀ (  q r : ZZ), a = b * q + r →  r > b,
have := WOP_Contradiction (euclidean) ,
have thing :(∀ (minimal : ZZ), ∃ (smaller : ZZ), ¬euclidean minimal → ¬euclidean smaller ∧ smaller < minimal)  := begin
intros minimal,
split, {
  intros em,
  change (¬euclidean minimal) with (∀ (a b q r :ZZ), (a=b*q+r)→  r > b) at  em,
  -- rw euclidean at em,
sorry,
},
sorry,
end,
 have that := this thing,
exact that,

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