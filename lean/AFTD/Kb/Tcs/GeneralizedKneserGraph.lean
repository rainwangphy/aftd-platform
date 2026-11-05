import AFTD.Prelude

/-!
# generalized_kneser_graph

Topic: graphs   Node: 2d89a144c988

Provenance: formalization of a published result. Source: arXiv:2611.04486 Sec. 1

The generalized Kneser graph KG(2n, n, r) is the simple graph whose vertices are the n-element subsets of Fin (2 * n), where two distinct subsets s and t are adjacent if and only if the cardinality of their intersection s ∩ t is strictly less than r.
-/

/-- The generalized Kneser graph KG(2n, n, r) whose vertices are n-element subsets of a (2n)-element ground set, adjacent when their intersection size is strictly less than r. -/
def generalized_kneser_graph (n r : ℕ) :
    SimpleGraph {s : Finset (Fin (2 * n)) // s.card = n} := {
  Adj := fun s t => s ≠ t ∧ (s.1 ∩ t.1).card < r
  symm := ⟨fun s t h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun s h => h.1 rfl⟩
}
