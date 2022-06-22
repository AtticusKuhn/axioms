-- def is_positive (n: \):Prop
import .integers
import .ring
variables { ZZ : Type} [integers ZZ ]
variable is_positive : ZZ → Prop



axiom pos_times_pos:  ∀( a b : ZZ), is_positive a → is_positive b → is_positive (a*b)
axiom pos_plus_pos:  ∀( a b : ZZ), is_positive a → is_positive b → is_positive (a+b)
axiom nontriviality:  ¬ is_positive(0)
axiom trichotomy:  ∀( a : ZZ), xor ( xor (is_positive a) (a=0) ) (is_positive (-a))

