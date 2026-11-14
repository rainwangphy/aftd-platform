import AFTD.Prelude

/-!
# kneser_compl

Topic: graphs   Node: d90265675732

Provenance: formalization of a published result. Source: arXiv:2611.17183, Section 3

The complement of the Kneser graph K(n, k) is the simple graph whose vertices are the k-element subsets of Fin n, with an edge between two distinct subsets if and only if they are not disjoint (they have nonempty intersection).
-/

/-- The complement of the Kneser graph K(n, k) on k-element subsets of Fin n. -/
def kneser_compl (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // s.card = k} where
  Adj s t := s ≠ t ∧ ¬ Disjoint s.1 t.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
