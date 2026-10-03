import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsObedientDirectScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility

/-!
# is_sender_optimal_scheme

Topic: mechanism_design   Node: b442da471fcf

q is obedient and maximises the sender's utility among obedient schemes.
-/

open Finset in
/-- `q` is obedient and maximises the sender's utility among obedient schemes. -/
def is_sender_optimal_scheme {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : (ι → Bool) → ℝ)
    (q : (ι → Bool) → (ι → Bool) → ℝ) : Prop :=
  is_obedient_direct_scheme μ q ∧
    ∀ q', is_obedient_direct_scheme μ q' → persuasion_sender_utility q' ≤ persuasion_sender_utility q
