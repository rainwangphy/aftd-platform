import AFTD.Prelude

/-!
# hunger3_fire

Topic: combinatorial_games   Node: 24cb5126188d

Provenance: helper lemma. step towards symmetric_hunger_tile_convex_iff_ultrametric_transition_three

One hunger step on a 3-by-3 real matrix with the firing index i prescribed: coordinate j becomes h j + Q i j, minus 1 if j = i.
-/

/-- The hunger step with a prescribed firing index, used to write the forced three-step trajectory of a firing cell. -/
noncomputable def hunger3_fire (Q : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (h : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => h j + Q i j - (if j = i then (1 : ℝ) else 0)
