import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoord
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenPrior
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenState

/-!
# bit_persuasion_even_prior_is_bit_prior

Topic: mechanism_design   Node: d0f97b126290

Provenance: helper lemma. arXiv:2606.22226

For every natural number m ≥ 1, the function bit_persuasion_even_prior m is a bit prior (is_bit_prior (bit_persuasion_even_prior m)).
-/

open Finset in
/-- For m ≥ 1, the two-layer prior on 2m states is a valid probability distribution on bit strings. -/
theorem bit_persuasion_even_prior_is_bit_prior (m : ℕ) (hm : 1 ≤ m) :
    is_bit_prior (bit_persuasion_even_prior m) := by
  refine ⟨fun x => sum_nonneg fun s _ => ?_, ?_⟩
  · split_ifs
    · positivity
    · exact le_refl 0
  · unfold bit_persuasion_even_prior
    rw [sum_comm]
    simp only [sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
