import AFTD.Prelude

/-!
# row_conflict_edges

Topic: streaming   Node: 79bf1d9cd731

Provenance: formalization of a published result. Source: arXiv:2611.14163, Lemma 4.1

For an n × m partial binary matrix P with entries in Option (Fin 2) and a finite set of columns C : Finset (Fin m), row_conflict_edges P C is the finite set of pairs (i₁, i₂) ∈ Finset (Fin n × Fin n) with i₁ < i₂ such that there exists a column j ∉ C with either P i₁ j = some 0 and P i₂ j = some 1, or P i₁ j = some 1 and P i₂ j = some 0.
-/

/-- The set of unordered row-conflict edge pairs (i₁, i₂) with i₁ < i₂ for rows of a partial binary matrix outside a set of columns C. -/
def row_conflict_edges {n m : ℕ} (P : Matrix (Fin n) (Fin m) (Option (Fin 2))) (C : Finset (Fin m)) :
    Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p =>
    p.1 < p.2 ∧ ∃ j, j ∉ C ∧ ((P p.1 j = some 0 ∧ P p.2 j = some 1) ∨ (P p.1 j = some 1 ∧ P p.2 j = some 0)))
