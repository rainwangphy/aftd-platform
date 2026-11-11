import AFTD.Prelude
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.IsOnlineColoringAlg

/-!
# op869_predecessor_causality

Topic: online_algorithms   Node: 999026f037d2

Provenance: helper lemma. arXiv:2610.41516, Sections 1 and 2; formal infrastructure for the adaptive online-coloring construction.

If two predecessor presentations agree through vertex i, any online coloring algorithm gives vertex i the same color on both graphs.
-/

theorem op869_predecessor_causality {n : ℕ} (A : SimpleGraph (Fin n) → Fin n → ℕ)
    (hA : IsOnlineColoringAlg A) (P Q : Fin n → Finset (Fin n)) (i : Fin n)
    (hPQ : ∀ j : Fin n, j ≤ i → P j = Q j) :
    A (op869_graph_from_predecessors P) i = A (op869_graph_from_predecessors Q) i := by
  apply hA
  intro j l hj hl
  simp only [op869_graph_from_predecessors]
  rw [hPQ j hj, hPQ l hl]
