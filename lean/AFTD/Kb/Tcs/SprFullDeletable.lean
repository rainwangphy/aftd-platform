import AFTD.Prelude

/-!
# spr_full_deletable

Topic: learning   Node: 274b377a1e2a

Provenance: helper lemma. step towards spr_linear_board_sharp_quadratic_saturation_horizon

The set of cells the labeler is allowed to empty when the pointer selects cell j: the minus signs to the left of j together with the plus signs to the right of j. Note it does not contain j itself.
-/

/-- The set of cells whose sign the labeler may delete after the pointer names j: minus signs left of j and plus signs right of j. -/
def spr_full_deletable {n : ℕ} (b : Fin n → Option Bool) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i < j ∧ b i = some false) ∨ (j < i ∧ b i = some true))
