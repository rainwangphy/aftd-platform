import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePrior

/-!
# persuasion_slice_prior_is_bit_prior

Topic: mechanism_design   Node: 046112252732

The slice prior is a probability distribution on {0,1}^ι.
-/

open Finset in
/-- The slice prior is a probability distribution on `{0,1}^ι`. -/
lemma persuasion_slice_prior_is_bit_prior (m : ℕ) : is_bit_prior (persuasion_slice_prior m) := by
  refine ⟨fun x => sum_nonneg fun s _ => ?_, ?_⟩
  · split_ifs
    · positivity
    · exact le_refl 0
  · unfold persuasion_slice_prior
    rw [sum_comm]
    simp only [sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
