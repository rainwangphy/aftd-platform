import AFTD.Prelude
import AFTD.Kb.Tcs.GridBoxFree

/-!
# grid_box_free_of_le

Topic: combinatorics   Node: 9fa1f5a46a6b

Provenance: helper lemma. arXiv:2611.19635 (Constructive and computational methods for extremal and near-extremal box colorings), Sec. 2

If $c' \le c$ and $f$ is a box-free $2$-coloring of $[a] \times [b] \times [c]$, then the restriction of $f$ to $[a] \times [b] \times [c']$ is also box-free.
-/

/-- The restriction of a box-free coloring to fewer layers remains box-free. -/
theorem grid_box_free_of_le {a b c c' : ℕ} (hle : c' ≤ c) {f : Fin a → Fin b → Fin c → Bool} (hf : grid_box_free f) : grid_box_free (fun x y (z : Fin c') => f x y (z.castLE hle)) := fun x₁ x₂ y₁ y₂ z₁ z₂ hx hy hz =>
  hf x₁ x₂ y₁ y₂ (z₁.castLE hle) (z₂.castLE hle) hx hy ((Fin.castLE_lt_castLE_iff hle).mpr hz)
