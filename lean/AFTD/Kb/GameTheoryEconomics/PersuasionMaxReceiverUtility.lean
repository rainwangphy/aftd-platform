import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSenderOptimalScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverUtility

/-!
# persuasion_max_receiver_utility

Topic: mechanism_design   Node: 0da6f33c91c6

R_max(μ): the largest receiver utility among sender-optimal obedient schemes.
-/

open Finset in
/-- `R_max(μ)`: the largest receiver utility among sender-optimal obedient schemes. -/
noncomputable def persuasion_max_receiver_utility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) : ℝ :=
  sSup {r | ∃ q, is_sender_optimal_scheme μ q ∧ r = persuasion_receiver_utility q}
