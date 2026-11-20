import AFTD.Prelude

/-!
# op874_four_color_pair_normalization

Topic: graphs   Node: 6712eb9d3033

Provenance: helper lemma. Color normalization for the OP-874 factor-word certificate.

Any two distinct colors in a four-color palette can be relabeled as colors zero and one.
-/

theorem op874_four_color_pair_normalization (a b : Fin 4) (hab : a ≠ b) : ∃ σ : Equiv.Perm (Fin 4), σ a = 0 ∧ σ b = 1 := by
  revert a b
  decide
