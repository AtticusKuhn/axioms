
import .ring
import .axiom_set
-- import tactic
open ring
variables {R : Type} [ring R]
variables {O : Type} [ordered_ring O ]


theorem div_self : ∀ (a  :R), a  ∣ a :=
begin
 intros a,
 rw divs,
 have : a*1=a := begin
  exact mul_one a,
 end,
 split,
  exact this ,

end

theorem div_mul : ∀ (a b c :R), a ∣ b → a ∣  b*c := begin
intros a b c d,
rw divs at d,
cases d,
rw divs,
split, {
  have  :  a * d_w *c = b *c := begin
  exact mul_right c d_h,
  end,
  rw mul_assoc at this,
exact this,
},
end

theorem divs_add: ∀ ( a b k :R ),  k ∣ a → k ∣ b → k ∣ (a+b) := begin
intros a b c d e,
rw divs at d,
rw divs at e,
cases d,
cases e,
rw divs,
split, {
 have :  c* d_w  + c*e_w = a +b := begin
 rw d_h,
 rw e_h,
 end,
 rw ← mul_add at this,
 exact this,
},
end

theorem divs_linear_combination: ∀(a b c d e:R ), a ∣ b → a ∣ c → a ∣ (b*d+c*e) := begin
intros a b c d e f g,
rw divs at f,
rw divs at g,
cases f,
cases g,
rw mul_right d at f_h,
end

theorem divs_trans : ∀ (a b c : R), a ∣ b → b ∣ c → a ∣ c := begin
intros a b c d e,
rw divs at d,
rw divs at e,
cases d,
cases e,
rw divs,
split, {
rw ← d_h at e_h,
rw mul_assoc at e_h,
exact e_h,
},
end

-- theorem divs_le: ∀ (a b : O), is_positive (a) → is_positive (b) → a ∣ b → a ≤ b := begin
-- intros a b c d e,
-- rw divs at e,
-- cases e,
-- rw less_eq,
-- end

theorem neg_one_mul_neg_one: (-1:R) * (-1:R) = 1 := begin
 simp,
 rw mul_one,
end
