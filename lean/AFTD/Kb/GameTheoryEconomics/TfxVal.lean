import AFTD.Prelude

/-!
# tfx_val

Topic: fair_division   Node: b0f0e8a754bd

The identical valuation used in the counterexample: good types z, a, b worth 0, 1, x.
-/

/-- The identical valuation used in the counterexample: good types `z, a, b` worth `0, 1, x`. -/
noncomputable def tfx_val (x : ℝ) : Fin 2 → Fin 3 → ℝ := fun _ => ![0, 1, x]
