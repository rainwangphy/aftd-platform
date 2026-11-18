import AFTD.Prelude
import AFTD.Kb.Tcs.GridBoxFree

/-!
# grid_box_free_max

Topic: combinatorics   Node: 127a32b4efa0

Provenance: formalization of a published result. Source: arXiv:2611.19635 (Constructive and computational methods for extremal and near-extremal box colorings), Def. 2.1

The parameter $N(a, b)$ is the maximum integer $c$ such that the grid $[a] \times [b] \times [c]$ admits an axis-parallel box-free $2$-coloring, defined as the supremum of all such $c$.
-/

/-- The maximum number of layers c such that [a] × [b] × [c] admits a box-free 2-coloring. -/
noncomputable def grid_box_free_max (a b : ℕ) : ℕ := sSup {c : ℕ | ∃ f : Fin a → Fin b → Fin c → Bool, grid_box_free f}
