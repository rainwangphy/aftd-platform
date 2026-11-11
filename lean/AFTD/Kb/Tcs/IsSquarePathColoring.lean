import AFTD.Prelude

/-!
# is_square_path_coloring

Topic: information   Node: 8b262606f4b5

Provenance: original. Related work: arXiv:2611.01064; Open Problem OP-1480

A word y : Fin n → Fin q is a square path coloring if y i ≠ y j for all i, j : Fin n with j.val = i.val + 1 or j.val = i.val + 2.
-/

/-- A word y : Fin n → Fin q is a square path coloring if adjacent elements and distance-two elements are distinct. -/
def is_square_path_coloring {n q : ℕ} (y : Fin n → Fin q) : Prop := ∀ (i j : Fin n), (i.val + 1 = j.val ∨ i.val + 2 = j.val) → y i ≠ y j
