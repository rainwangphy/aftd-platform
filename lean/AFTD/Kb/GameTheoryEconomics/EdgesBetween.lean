import AFTD.Prelude

/-!
# edges_between

Topic: fair_division   Node: 94bedf670c50

The parallel class of edges joining agents i and j.
-/

/-- The parallel class of edges joining agents `i` and `j` (the items in `E_i ∩ E_j`). -/
def edges_between {m n : ℕ} (ends : Fin m → Fin n × Fin n) (i j : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => ends e = (i, j) ∨ ends e = (j, i)
