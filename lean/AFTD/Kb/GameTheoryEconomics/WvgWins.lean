import AFTD.Prelude

/-!
# wvg_wins

Topic: general_equilibrium   Node: 1dba796bff99

A coalition wins in the weighted voting game (w; q) with strict quota if its total weight exceeds q.
-/

/-- A coalition `C` wins in the weighted voting game `(w; q)` with a strict quota (How Banzhaf Makes a Victor, Sec. 2.1): its total weight exceeds `q`. -/
abbrev wvg_wins {n : ℕ} (w : Fin n → ℝ) (q : ℝ) (C : Finset (Fin n)) : Prop :=
  q < ∑ i ∈ C, w i
