import .myRing
import .set_1
import tactic.basic
import init.default
import logic.basic
-- import tactic
open myRing
variables {R : Type} [myRing R]
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
  have  wop := WOP (λ x, ¬ prop(x)),
  have wopsome: ∃ (some : ZZ), (λ (x : ZZ), ¬prop x) some := begin
  use all,
  end,
  have wop_holds := wop wopsome,
  cases wop_holds with minimal rest,
  cases rest with nminimal other,
  have smaller := holds_for_smaller minimal,
  cases smaller with smaller smallereq,
  have contra := smallereq nminimal,
  cases contra with not_smaller smaller_lt_minimal,
  -- cases smallereq with _ smaller_lt_minimal,
  have min_le_smaller := other smaller not_smaller,
  rw less_eq at min_le_smaller,
  cases min_le_smaller, {
    have tr := trans_lt smaller_lt_minimal min_le_smaller,
    apply no_lt_self smaller,
    exact tr,
  },
  rw min_le_smaller at smaller_lt_minimal,
      apply no_lt_self smaller,
exact smaller_lt_minimal,
end 

theorem divs_le: ∀ (a b: O ), is_positive a  → is_positive b → a ∣ b → a ≤ b := begin
  intros a b a_pos b_pos a_div_b,
  rw divs at a_div_b,
  cases a_div_b with p eq,{
 have p_pos  := pos_div_pos a b p a_pos b_pos eq,

  have eq : p*(a-1) +p = b,{
    rw subtr,
    rw mul_add ,
    rw mul_comm p (-1),
    rw mul_neg_one,
    rw add_assoc,
    rw add_comm (-p) (p),
    rw add_neg,
    rw add_zero,
    rw mul_comm,
    exact eq,
  },

    sorry,
  },
 
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
theorem zlt1: (0:ZZ) < (1:ZZ) := begin
rw less_than,
-- left,
-- rw less_than,
use 1,
split,
exact one_pos,
rw zero_add,
end
theorem ge1pos: ∀ (x:ZZ), 1 ≤ x → is_positive x := begin 
intros x olex,
rw pos_is_g0,
rw less_eq at olex,
cases olex,{
have g : (0:ZZ) < 1, {
  exact zlt1,
},
have := trans_lt g olex,
exact this,
},
rw ← olex,
exact zlt1,
end
theorem gcd_pos: ∀ (a b : ZZ), is_positive (gcd a b) := begin
intros a b,
let d :ZZ := gcd a b,
-- rw d,
have := gcd_def a b d ,
have thing : gcd a b =d := begin
refl,
end,
rw this at thing,
rcases thing with ⟨diva,divb, biggest⟩,  
have big : 1 ≤ d := begin
have biggerthan1:= biggest 1,
have divboth: 1 ∣ a ∧ 1 ∣ b, {
exact ⟨ div_one a,div_one b⟩ 
},
have bruh := biggerthan1 divboth,
exact bruh,
end,
have thing2 : gcd a b =d := begin
refl,
end,
rw thing2,
exact ge1pos d big,
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
  cases others_right with others_left others_right,
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
theorem pos_iff_le_one: ∀(a :ZZ), is_positive a ↔ 1 ≤ a := begin
intro a,
split,{
intro pa,
rw less_eq,
have := pos_is_g0 a,
 have z_le_a : 0 < a,{
   rw less_than,
   use a,
   rw zero_add,
   split,
   exact pa,
   refl,
 },
 have nibzo := NIBZO,
 have trich := trichotomy_lt a 1,
 rcases trich with ⟨one,two,three⟩, {
   exfalso,
   apply nibzo,
   use a,
   change (0<a ∧ a < 1),
   split,
   exact z_le_a,
   exact one,
 },
 rcases trich with ⟨one,two,three⟩, {
   right,
   symmetry,
   exact two,
 },
 rcases trich with ⟨one,two,three⟩, {
   left,
   exact three,
 },
},
intro a_le_one,
rw less_eq at a_le_one,
-- rw 
cases a_le_one with l r,{
rw less_than at l,
rcases l with ⟨g,h,j⟩ ,
have pp := pos_plus_pos one_pos h,
rw ← j,
exact pp,
},
rw ← r,
exact one_pos,
end
theorem le_le_eq: ∀( a b: O), a ≤ b → b ≤ a → a = b := begin
  intros d min d_le_min min_le_d,
  rw less_eq at d_le_min,
    rw less_eq at  min_le_d,
    cases d_le_min, {
      cases min_le_d, {
        have tr := trans_lt d_le_min min_le_d,
        exfalso,
        apply no_lt_self d,
        exact tr,
      },
      rw ← min_le_d at d_le_min,
       exfalso,
        apply no_lt_self min,
        exact d_le_min,
    },
    exact d_le_min,
end
theorem push_not_exists: ∀{x : Type}, ∀{p: x→ Prop}, (¬ (∃(q : x), p(q))) ↔ (∀ (q : x), ¬ p(q)):=
begin
  intros x p,
  split,
  {
    intros h q pq,
    apply h,
    split,
    exact pq,
  },
  {
    intros h pq,
    cases pq with q pq,
    apply h q,
    exact pq,
  }
end
theorem push_and: ∀{p q : Prop}, (¬ (p ∧ q)) ↔ (¬ p ∨ ¬ q):=
begin
  intros p q,
  split,
  {
    intro hpq,
    by_cases q,
    {
      left,
      intro j,
      apply hpq,
      exact ⟨j, h⟩,
    },
    {
      right,
      exact h,
    }
  },
  {
    intro pq,
    intro paq,
    cases pq,
    apply pq,
    exact paq.1,
    apply pq,
    exact paq.2,
  }
end
theorem not_le_ge: ∀{a b : O}, (¬ (a < b)) ↔ ( b ≤ a):=
begin
  intros a b,
  split,
  {
    intro ab,
    cases trichotomy_lt a b,
    {
      exfalso,
      apply ab,
      exact h.1,  
    },
    cases h,
    {
      rw h.2.1,
      rw less_eq,
      right,
      refl,
    },
    {
      rw less_eq,
      left,
      exact h.2.2,
    }
  },
  {
    intros ba h,
    --rw less_than at h,
    rw less_eq at ba,
    cases ba,
    {
      have := trans_lt h ba,
      apply no_lt_self a,
      exact this,
    },
    {
      rw
      ba at h,
      apply no_lt_self a,
      exact h,
    },
  }
end
lemma refl_le : ∀(a: O), a ≤ a :=
begin 
  intro a,
  rw less_eq,
  right, 
  refl,
end
theorem sub_both_lt: ∀(a b x: O), ((a <  b)) ↔ ( a-x < b-x):=
begin
sorry,
end
theorem min_1_lt_self: ∀ (x: O), x-1 < x := begin
intro x,
rw less_than,
use 1,
split,
exact one_pos,
rw subtr,
rw add_assoc,
rw add_comm (-1:O),
rw add_neg,
rw add_zero,
end
theorem sub_both_le: ∀(a b x: O), ((a ≤  b)) ↔ ( a-x ≤ b-x):=
begin
  intros a b x,
  split,
  {
    intro ab,
    have := add_le_add ab (refl_le (-x)),
    rw subtr,
    rw subtr,
    exact this, 
  },
  {
    intro axb,
    have := add_le_add axb (refl_le x),
    rw subtr at this,
    rw subtr at this,
    rw add_assoc at this,
    rw add_assoc at this,
    rw add_comm (-x) at this,
    rw add_neg at this,
    rw add_zero at this,
    rw add_zero at this,
    exact this,
  }
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
  intros a b c,
  split,
  {
    intro h,
    rw less_than at h,
    cases h with P q,
    cases q with Ppos s,
    rw add_assoc at s,
    have := left_cancel s,
    rw less_than,
    split,
    split,
    exact Ppos,
    exact this,
  },
  {
    intro ab,
    rw less_than at ab,
    cases ab with P,
    cases ab_h with Ppos h,
    rw less_than,
    split, split,
    exact Ppos,
    rw ← h,
    rw add_assoc,
  }
end
@[simp]
theorem neg_comp: ∀(a b: O), -a < -b ↔ b < a:=
begin
intros a b,
split, {
intros na_le_nb,
rw less_than at na_le_nb,
cases na_le_nb with p na_le_nb,
cases na_le_nb with p_pos na_le_nb,
rw add_comm at na_le_nb,
have move := move na_le_nb,
rw less_than,
use p,
split,{
  exact p_pos,
},
rw move,
rw ←  add_assoc,
rw add_neg,
rw zero_add,
rw neg_neg_a,
},
intros b_lt_a,
rw less_than at b_lt_a,
rcases b_lt_a with ⟨w,x,y,z⟩,
rw less_than,
use w,
split,
exact x,
rw dist_neg_add,
rw add_assoc,
rw add_comm (-w) w,
rw add_neg,
rw add_zero,
end
theorem demorgan: ∀(p q :Prop), ¬(p ∨ q ) → (¬ p ∧ ¬ q) := begin
intros p q n_p_or_q,
split, {

by_contradiction,
apply n_p_or_q,
left,
exact h,
},
by_contradiction,
apply n_p_or_q,
right,
exact h,
end
theorem not_le_iff_ge: ∀(a b: O), a < b ↔ ¬ (b ≤  a):=
begin
intros a b,
split, {
  intros a_le_b,
  by_contradiction,
  rw less_eq at h,
  cases h, {
    have tr := trans_lt a_le_b h,
    apply no_lt_self a,
    exact tr,
  },
  rw h at a_le_b,
   apply no_lt_self a,
    exact a_le_b,
},
intro n_b_le_a,
rw less_eq at n_b_le_a,
have dm := demorgan (b<a) (b=a) n_b_le_a,
cases dm with n_b_le_a n_b_eq_a,
-- rw demorgan at n_b_le_a,
have trich := trichotomy_lt a b,
rcases trich with ⟨s,d,f⟩, {
exact s,
},
rcases trich with ⟨s,d,f⟩, {
exfalso,
apply  n_b_eq_a,
symmetry,
exact d,
},
rcases trich with ⟨s,d,f⟩, {
  exfalso,
  apply n_b_le_a,
  exact f,
},
end


theorem Euclidean_Algorithm_One_Step_two: ∀ (a b: ZZ),  is_positive a → is_positive b → ∃ (q r :ZZ), a=b*q+r ∧ r < b ∧ 0 ≤ r :=
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
rw push_and at contradict,
cases contradict,{
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
 cases min_smaller_other with x min_smaller_other,
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
cases min_smaller_other with min_pos garbage,
have thing := pos_is_g0 min,
rw thing at min_pos,
apply contradict,
rw less_eq,
left,
exact min_pos

-- sorry,

},

},
-- exact q,
end
/-

Fix $a$ and $b$.
Consider the set 
$$S= \{ax+by \mid ax+by \ge 0, x,y \in \ZZ \}.$$
$S$ is non-empty because $a \in S$.
All elements  of $S$ are positive by construction. This means $S$ has a minimal element, call it $m$ by WOP.  By the construction of $m$, let 
$$m=ax'+by'$$
for some integers $x',y'$.
By lemma \ref{l:ES}, there exists integers
$q,r$ such that $a=mq+r$ and $0 \le r < m$.
Since $r < m$ and $m$ is the minimal element
of $S$, it follows that $r \not\in S$.
By algebraic manipulation, we have
$$r=a-mq=a-(ax'+by')q=a-ax'-by'q = a(1-x')+b(-y'a).$$

We find that $r$ is expressible as $ax+by$ (with $x=1-x'$ and $y=-y'a$), so the only
way that $r\not\in S$ is that $r \le 0$.
By construction, we know $r \ge 0$, so this
means $r=0$. This gives us that
$0=a-mq \implies a=mq$, which gives that
$m \mid a$ by Definition \ref{def:divs}. 
By similar reasoning, we can deduce $m \mid b$.
Let $d=gcd(a,b)$.
% Since
% $m \mid a$ and $m \mid b$, therefore $m \mid d$ by Theorem \ref{thm:divsgcd}.
 By the definition of GCD,
we have $d \mid a$ and $d \mid b$. This means
by Theorem \ref{thm:lincombdivs} that $d \mid (ax'+by')$. But $ax'+by'=m$, so $d\mid m$.
% By Theorem \ref{thm:divsequal}, 
By Lemma \ref{lem:div_lt}, we have $d \le m$.
But $m$ is a common divisor of both
$a$ and $b$, so by Definition \ref{def:gcd}, $d \ge m$.
The only possibility is that $d=m$.
We have $m=d$.
This means that there exists $x,y$ such that
$ax+by = gcd(a,b)$, and in addition, $gcd(a,b)$
is the smallest positive combination of $a,b$.

-/
theorem BezoutsLemma: ∀ (a b : ZZ), is_positive a → is_positive b → ∃ (x y : ZZ), a*x+b*y = gcd a b := begin
intros a b a_positive b_positive,
  let WOP_prop : ZZ → Prop := λ s, ∃ (x y : ZZ), a*x + b*y = s ∧ is_positive s,
  have WOP := explicit_WOP WOP_prop,
  have WOP_a :  WOP_prop a, {
    change (∃ (x y : ZZ), a*x + b*y = a ∧ is_positive a),
    split, {
      split, {
        have a_works: a * 1 + b * 0 = a , {
          simp,
          rw mul_one,
          rw add_zero,
        },
        split,
        exact a_works,
        exact a_positive,
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
  change (∃ (x' y' : ZZ), a*x' + b*y' = min ∧ is_positive min) at WOP_Min,
  cases WOP_Min with x' rest,
    cases rest with y' rest,

  -- have mo
  cases others_smaller with min_pos stuff,
  have euclidean_min := Euclidean_Algorithm_One_Step_two a min a_positive min_pos,
  cases euclidean_min with q rest,
  cases rest with r eq,
  cases eq with eq ineq,
  cases rest with rest axas,
  have thing:  r= a-min*q, {
    have rev : min * q + r = a, {symmetry,exact eq},
    rw add_comm at rev,
    have m:= move rev,
    rw subtr,
    exact m,
  },
  have thing2:  r = a - (a*x' + b*y')*q, {
    rw ← rest at thing,
    exact thing,
  },
  rw mul_comm at thing2,
  rw mul_add at thing2,
  have thing3 : r = a*(1-q*x')  +  (b *(-q* y')), {
    rw subtr,
    rw mul_add,
    rw mul_one,
    rw ← dist_neg_left,
    rw ← mul_assoc,
    rw mul_comm a (-q),
    rw mul_assoc,
    rw ← mul_assoc b (-q) y',
    rw mul_comm b (-q),
    rw mul_assoc,
    rw add_assoc,
    rw ← mul_add,
    rw dist_neg_left,
    rw ← subtr,
    rw mul_add,
    exact thing2,
  },
  have rnotpos: ¬ (is_positive r), {
    intro h,
    -- rw pos_is_g0 r at h,
    have wop_prop_r : WOP_prop r,
    {
      split,
      split,
      split,
      symmetry,
      exact thing3,
      exact h,
    },
    have rlemin := stuff r wop_prop_r,
    rw less_eq at rlemin,
    cases rlemin,
    have := trans_lt ineq.1 rlemin,
    apply no_lt_self r,
    exact this,
    cases ineq,
    rw rlemin at ineq_left,
    apply no_lt_self r,
    exact ineq_left,
  },
  have r_is_0: r=0, {
    cases ineq with r_lt_min zero_le_r,
    rw less_eq at zero_le_r,
    cases zero_le_r,{
      rw pos_is_g0 at rnotpos,
      rw not_le_ge at rnotpos,
      rw less_eq at rnotpos,
      cases rnotpos with zer les,{
        have t := trans_lt zer zero_le_r,
        exfalso,
        apply no_lt_self r,
        exact t,
      },
      exact les,
    },
    symmetry,
    exact zero_le_r,
  },
  let d:ZZ  := gcd a b,
  have min_div_a : min ∣ a,{
    rw r_is_0 at eq,
    rw add_zero at eq,
    rw divs,
    split,
    symmetry,
    exact eq,
  },
  have euclidean_min2 := Euclidean_Algorithm_One_Step_two b min b_positive min_pos,
  cases euclidean_min2 with q2 rest2,
  cases rest2 with r2 eq2,
  cases eq2 with eq2 ineq2,
  have iter:  r2 = b - min*q2, {
    have rev : min * q2 + r2 = b, {symmetry,exact eq2},
    rw add_comm at rev,
    have m:= move rev,
    rw subtr,
    exact m,
  },
  have iter2:  r2 = b - (a*x' + b*y')*q2, {
    rw ← rest at iter,
    exact iter,
  },
  rw mul_comm at iter2,
  rw mul_add at iter2,
  have iter3 : r2 = a*(-q2 * x')  +  (b *(1 - q2* y')), {
    rw subtr,
    rw mul_add,
    rw mul_one,
    rw ← dist_neg_left,
    rw ← mul_assoc,
    rw mul_comm a (-q2),
    rw ← add_assoc,
    rw add_comm ((-q2) * a * x') b,
    rw ← mul_assoc b,
    rw mul_comm b,
    rw add_assoc,
    rw mul_assoc,
    rw mul_assoc,
    rw ← mul_add,
    rw dist_neg_left,
    rw ← subtr,
    rw mul_add,
    exact iter2,
  },
  have r2notpos: ¬ (is_positive r2), {
    intro h,
    -- rw pos_is_g0 r at h,
    have wop_prop_r2 : WOP_prop r2,
    {
      split,
      split,
      split,
      symmetry,
      exact iter3,
      exact h,
    },
    have r2lemin := stuff r2 wop_prop_r2,
    rw less_eq at r2lemin,
    cases r2lemin,
    have := trans_lt ineq2.1 r2lemin,
    apply no_lt_self r2,
    exact this,
    cases ineq2,
    rw r2lemin at ineq2_left,
    apply no_lt_self r2,
    exact ineq2_left,
  },
  have r2_is_0: r2=0, {
    cases ineq2 with r2_lt_min zero_le_r2,
    rw less_eq at zero_le_r2,
    cases zero_le_r2,{
      rw pos_is_g0 at r2notpos,
      rw not_le_ge at r2notpos,
      rw less_eq at r2notpos,
      cases r2notpos with zer les,{
        have t := trans_lt zer zero_le_r2,
        exfalso,
        apply no_lt_self r2,
        exact t,
      },
      exact les,
    },
    symmetry,
    exact zero_le_r2,
  },
   have min_div_b : min ∣ b,{
    rw r2_is_0 at eq2,
    rw add_zero at eq2,
    rw divs,
    split,
    symmetry,
    exact eq2,
  },
  have d_div: d ∣ (a*x'+b*y'),{
    have dcons := gcd_def a b d,
    cases dcons with useful junk, 
    have keyd : gcd a b = d := by refl,
    cases useful keyd,
    cases right with r junk2,
    exact divs_linear_combination x' y' left r,
  },
  have d_div_min: d ∣ min, {
    rw ← rest,
    exact d_div,
  },
  have d_pos: is_positive d := begin
    change (is_positive (gcd a b)),
    exact gcd_pos a b,
    -- sorry,
  end,
  have d_le_min: d ≤ min, {

     exact divs_le d min d_pos axas  d_div_min,
    -- sorry,
  },
  have min_le_d: min ≤ d, {
    have dcons := gcd_def a b d,
    have keyd : gcd a b = d := by refl,
    cases dcons with useful junk,
    cases useful keyd,
    cases right with junk2 u,
    have fin := u min,
    apply fin,
    exact ⟨min_div_a, min_div_b⟩,
  },
  have min_eq_d: min = d, {
      exact le_le_eq min d  min_le_d d_le_min,
  },
  split, {
    split, {
        have final:a * x' + b * y' = d  := begin
       rw ← min_eq_d,
       exact rest,
        end,
        have same: gcd a b =d, {refl},
        rw same,
        exact final,
    },
  },
end

theorem Fundamental_Lemma: ∀ (a b c:ZZ), a ∣ (b*c) → gcd a b = 1 → is_positive a → is_positive b → a ∣ c := begin
intros a b  c a_div_bc gcd_a_b a_pos b_pos,
have bezout := BezoutsLemma a b a_pos b_pos,
rcases bezout with ⟨x,y,equation ⟩,
rw gcd_a_b at equation,
rw divs at a_div_bc,
rcases a_div_bc with ⟨p, eq ⟩,
have mulled : a * x *c + a * p * y = c, {
rw eq,
-- rw mul_assoc a p y,
rw mul_comm (a*x) c,
rw mul_assoc b c y,

rw mul_comm (b) (c*y),
rw  mul_assoc c y b,
rw ← mul_add,
have mulled_equation := mul_left c equation,
rw mul_one at mulled_equation,
rw mul_comm y b,
exact mulled_equation,
},
rw mul_assoc at mulled,
rw mul_assoc at mulled,
rw ←  mul_add at mulled,
rw divs,
use (x * c + p * y),
exact mulled,
end
axiom pi: ZZ → ZZ → (ZZ → ZZ) →ZZ

axiom pi_same: ∀{x :ZZ}, ∀{f : ZZ → ZZ}, pi x x f = f x 
axiom pi_diff: ∀{x y :ZZ}, ∀{f : ZZ → ZZ}, pi x y f = (f y) * (pi x (y -1) f)

axiom is_prime:  ZZ → Prop
axiom prime:
  ∀ (n:ZZ),
    is_prime n 
    ↔ is_positive n ∧ 
    (∀(d:ZZ), 
      is_positive d →  
      d ∣ n →  (d=1 ∨ d=n))

theorem twoPositive: is_positive (2:ZZ) := begin
exact pos_plus_pos one_pos one_pos,
end
theorem zle1: (0:ZZ) ≤ (1:ZZ) := begin
rw less_eq,
left,
rw less_than,
use 1,
split,
exact one_pos,
rw zero_add,
end

theorem npos_le_0: ∀(x:ZZ), ¬(is_positive x) ↔ x ≤ 0 := begin
intro x,

split,{
  intro np,
  have := not_le_ge ,
  cases this,
  apply this_mp,
  have p := pos_is_g0 x,
  by_contradiction,
  cases p,
  have := p_mpr h,
  apply np,
  exact this,
},
intro zlex,
rw less_eq at zlex,
cases zlex,{
    have p := pos_is_g0 x,
cases p,
by_contradiction,
-- 
have := p_mp h,
have := trans_lt zlex this,
apply no_lt_self x,
exact this,
},
rw zlex,
exact nontriviality,
end
theorem prime_gcd: ∀ (p a : ZZ),is_positive a →  is_prime p → ¬ (p ∣ a) → gcd p a = 1 := begin
  intros  p a  a_pos pprime ndiv,
  have gcdax := gcd_def p a 1,
  have primedef := prime p,
  rw primedef at pprime,
  rw gcdax,
  split,
  exact div_one p,
  split,
  exact div_one a,
  intros d ddiv,
  cases ddiv with dlp dla,
  cases pprime with ppos pprime,
  have dprime := pprime d,
  by_cases (is_positive d),{
  have x:= dprime h dlp,
  cases x with deq1 deqp,{
    rw deq1,
    exact refl_le 1,
  },
  exfalso,
  apply ndiv,
  rw ← deqp,
  exact dla,
  },
  have := npos_le_0 d,
  rw this at h,
  have zle := zle1,
{
  have lt := trans_le h zle,
  exact lt,
},
end
theorem prime_divs: ∀(p a b:ZZ), is_prime p → is_positive a → p ∣ (a*b) → (p ∣ a ∨ p ∣ b) := begin
intros p a b p_prime a_pos p_divs_ab,
  by_cases (p ∣ a),{
    left,
    exact h,
  },
 
  have  gcd1 := prime_gcd p a a_pos p_prime h,
   rw prime at p_prime,
  cases p_prime,
  have p_divides_b := Fundamental_Lemma p a b p_divs_ab gcd1 p_prime_left a_pos,
  right,
  exact p_divides_b,
end


theorem IHateLogic: ∀ {p q :Prop}, ¬ (p → q) → p → (¬ q) := begin
intros p q npq p,
by_contradiction,
apply npq,
intro a,
exact h,
end

theorem EuclidsLemma: ∀ (f : ZZ → ZZ), ∀(p n:ZZ), is_prime p → (∀ (x:ZZ), is_positive (f x)) →  p ∣ (pi 0 n f) → (∃(k:ZZ), p ∣ (f k)) := begin
intros f p n prime_p always_pos p_div_pi,
  let WOP_prop : ZZ → Prop := λ n, p ∣ (pi 0 n f) →   (∃ (k : ZZ), (p ∣ f k)),
  have wop_contra := WOP_Contradiction WOP_prop,
  have wop_inside: (∀ (minimal : ZZ), ∃ (smaller : ZZ), ¬WOP_prop minimal → ¬WOP_prop smaller ∧ smaller < minimal) := begin
  -- assume there is some minimal m for which Euclid's Lemma Doesn't Hold
  intros minimal,
  -- we are going to show that Euclid's Lemma doesn't hold for m-1
  use (minimal-1),
  -- introduce the proposition that Euclid's Lemma doesn't hold on m
    intros nminimal,

     have x := IHateLogic nminimal,
     rw push_not_exists at x,
     rw pi_diff at x,
     have pos_f:is_positive (f minimal) :=begin
  exact always_pos minimal,
     end,
     have zjhchas := prime_divs p (f minimal) (pi 0 (minimal - 1) f) prime_p pos_f ,
     split,{
intro prop_mminimal,
change ( p ∣ (pi 0  (minimal-1 ) f) →   (∃ (k : ZZ), (p ∣ f k))) at  prop_mminimal,
apply nminimal,
{
change ( p ∣ (pi 0  (minimal ) f) →   (∃ (k : ZZ), (p ∣ f k))),
intro holds_min,
rw ← pi_diff at zjhchas ,
rw ← pi_diff at x ,

have holder := zjhchas holds_min,
have holderx := x holds_min,
cases holder, {
  have contrdict_thing := holderx minimal,
  exfalso,
  apply contrdict_thing,
  exact holder,
},
have thing := prop_mminimal holder,
exact thing,

},
     },
    exact min_1_lt_self minimal,
  end,
  have w := wop_contra wop_inside n p_div_pi,
exact w,
end 

theorem composite_has_fact: ∀(x:ZZ), is_positive x →  ¬ (is_prime x) → (∃(d:ZZ), d ∣ x ∧ d ≠ 1 ∧ d ≠ x) := begin
intros  x pos not_prime,
by_contradiction,
rw push_not_exists at h,
-- rw push_and at h,
apply not_prime,
rw prime x,
-- intros pos
split,
{
  exact pos,
},
intros d dpos ddivx,
have := h d,
by_contradiction f,
have dm := demorgan (d = 1) (d=x) f,
apply this,
split,
exact ddivx,
exact dm,
end

theorem All_Integers_Have_Prime_Factor: ∀(x:ZZ), ∃ (p:ZZ), is_prime p → p ∣ x := begin
  intros x,
    let WOP_prop : ZZ → Prop := λ x, ∃(p:ZZ), is_prime p → p ∣ x,
  have wop_contra := WOP_Contradiction WOP_prop,
  have wop_inside: (∀ (minimal : ZZ), ∃ (smaller : ZZ), ¬WOP_prop minimal → ¬WOP_prop smaller ∧ smaller < minimal) := begin
  intros minimal,
split,{
  intro not_min,
  change (¬  (∃(p:ZZ), is_prime p → p ∣ minimal)) at not_min,
  rw push_not_exists at not_min,
  have nminimal := not_min minimal,
  push_neg at nminimal,
  cases nminimal, {
exfalso,
apply nminimal_right,
exact div_self minimal,
  },
},
exact minimal,
end,
  have w := wop_contra wop_inside  x,
exact w,
end
theorem All_Integers_Have_Prime_Repr: ∀(x:ZZ), ∃ (f:ZZ → ZZ),∃(n:ZZ), (∀ (i:ZZ), is_prime (f i) ) → pi 0 n f = x := begin
intros x,
    let WOP_prop : ZZ → Prop := λ x,  ∃ (f:ZZ → ZZ),∃(n:ZZ), (∀ (i:ZZ), is_prime (f i) ) → pi 0 n f = x ,

 have wop_contra := WOP_Contradiction WOP_prop,
  have wop_inside: (∀ (minimal : ZZ), ∃ (smaller : ZZ), ¬WOP_prop minimal → ¬WOP_prop smaller ∧ smaller < minimal) := begin
  intros min,
  split, {
    intros nmin,
    change  (¬ (∃ (f : ZZ → ZZ) (n : ZZ), (∀ (i : ZZ), is_prime (f i)) → pi 0 n f = min)) at nmin,
    rw push_neg.not_exists_eq at nmin,
sorry,
  },
sorry,
end,
  have w := wop_contra wop_inside  x,
exact w,
end
