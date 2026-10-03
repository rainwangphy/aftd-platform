import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionObedienceCost

/-!
# is_obedient_direct_scheme

Topic: mechanism_design   Node: 073ef9aa8712

An obedient direct scheme for the prior μ on {0,1}^ι.
-/

open Finset in
/-- An obedient direct scheme for the prior `μ` on `{0,1}^ι`. -/
def is_obedient_direct_scheme {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : (ι → Bool) → ℝ)
    (q : (ι → Bool) → (ι → Bool) → ℝ) : Prop :=
  (∀ x a, 0 ≤ q x a) ∧ (∀ x, ∑ a, q x a = μ x) ∧
    ∀ a i, ∑ x, q x a * persuasion_obedience_cost i x a ≤ 0
