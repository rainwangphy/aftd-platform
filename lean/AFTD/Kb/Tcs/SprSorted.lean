import AFTD.Prelude

/-!
# spr_sorted

Topic: learning   Node: 169af3188bcf

Provenance: helper lemma. step towards spr_linear_board_sharp_quadratic_saturation_horizon

A board is sorted if every plus sign sits to the left of every minus sign: for all cells i, j, if b i is a plus and b j is a minus then i < j.
-/

/-- A board is sorted when every plus sign lies to the left of every minus sign. -/
def spr_sorted {n : ℕ} (b : Fin n → Option Bool) : Prop :=
  ∀ i j : Fin n, b i = some true → b j = some false → i < j
