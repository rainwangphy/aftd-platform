import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset

/-!
# PMPoset.Width2

Topic: algorithms   Node: 8b892303617c

The poset has width at most 2: among any three distinct elements some two are comparable.
-/

/-- The poset has width at most `2`: among any three distinct elements some two are comparable. -/
def PMPoset.Width2 {n : ℕ} (P : PMPoset n) : Prop :=
  ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
    P.lt a b = true ∨ P.lt b a = true ∨ P.lt b c = true ∨ P.lt c b = true ∨
      P.lt a c = true ∨ P.lt c a = true
