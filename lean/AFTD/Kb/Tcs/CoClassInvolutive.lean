import AFTD.Prelude
import AFTD.Kb.Tcs.CoClass

/-!
# co_class_involutive

Topic: complexity_basics   Node: 67a0e33395a7

The complement operation on complexity classes is an involution: a language L is in co(co(C)) if and only if L is in C.
-/

/-- The co-class operation is involutive: co(co(C)) = C. -/
theorem co_class_involutive {α : Type*} (C : Language α → Prop) (L : Language α) :
    CoClass (CoClass C) L ↔ C L := by
  dsimp [CoClass]
  rw [compl_compl]
