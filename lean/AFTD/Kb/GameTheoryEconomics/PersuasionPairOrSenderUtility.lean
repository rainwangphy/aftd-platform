import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrScheme

/-!
# persuasion_pair_or_sender_utility

Topic: mechanism_design   Node: e72a5380308d

Sender utility of a pair-OR scheme.
-/

open Finset in
/-- Sender utility of a pair-OR scheme. -/
lemma persuasion_pair_or_sender_utility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : (ι → Bool) → (ι → Bool) → ℝ) :
    persuasion_sender_utility (persuasion_pair_or_scheme ν) =
      ∑ x, ∑ y, ν x y * ((Finset.univ.filter (fun i => (x i || y i) = true)).card : ℝ) := by
  classical
  unfold persuasion_sender_utility persuasion_pair_or_scheme
  apply sum_congr rfl; intro x _
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro y _
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq]
  simp
