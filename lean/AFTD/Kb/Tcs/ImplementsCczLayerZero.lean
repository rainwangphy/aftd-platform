import AFTD.Prelude
import AFTD.Kb.Tcs.ImplementsCczLayer

/-!
# implements_ccz_layer_zero

Topic: quantum   Node: 2fdde417f627

Provenance: original.

Sanity check: with no CCZ gates and no ancillas, the empty circuit implements the (identity) layer.
-/

theorem implements_ccz_layer_zero : implements_ccz_layer 0 0 [] := by
  unfold implements_ccz_layer
  use 0
  intro x z
  change (1 : Matrix (Fin (3 * 0 + 0) → Bool) (Fin (3 * 0 + 0) → Bool) ℂ) z _ = _
  rw [Matrix.one_apply]
  split_ifs <;> simp
