import AFTD.Prelude
import AFTD.Kb.Tcs.IntCrescentConfig
import AFTD.Kb.Tcs.IntCrescentPointInjective
import AFTD.Kb.Tcs.IntCrescentPoint

/-!
# int_crescent_config_card

Topic: combinatorics   Node: 0f7c7553c080

Provenance: helper lemma. arXiv:2610.38368 Section 3

For every integer n ≥ 3, the cardinality of the finite set int_crescent_config n is n.
-/

/-- The cardinality of int_crescent_config n is n for n ≥ 3. -/
theorem int_crescent_config_card (n : ℕ) (hn : 3 ≤ n) :
    (int_crescent_config n).card = n := by
  rw [int_crescent_config, Finset.card_image_of_injective _ (int_crescent_point_injective n hn),
    Finset.card_univ, Fintype.card_fin]
