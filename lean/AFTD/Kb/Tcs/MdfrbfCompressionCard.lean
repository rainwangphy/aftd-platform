import AFTD.Prelude

/-!
# mdfrbf_compression_card

Topic: combinatorics   Node: 2fae023b0b54

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

If W is a set of j-1 points of Fin d (j ≥ 2), then the complement of W has exactly d - (j-1) elements, so it can be reindexed by Fin (d - (j-1)).
-/

/-- The complement of the compressed block has the cardinality used to reindex Fin (d - (j-1)). -/
theorem mdfrbf_compression_card (j d : ℕ) (hj : 2 ≤ j) (W : Finset (Fin d)) (hW : W.card = j - 1) :
    Fintype.card ↥(Finset.univ \ W) = d - (j - 1) := by
  rw [Fintype.card_coe, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
      Finset.inter_univ, hW]
