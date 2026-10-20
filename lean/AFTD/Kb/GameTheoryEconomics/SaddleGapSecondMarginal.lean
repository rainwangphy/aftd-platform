import AFTD.Prelude

/-!
# saddle_gap_second_marginal

Topic: equilibria   Node: 3a748d5ab7e6

Provenance: formalization of a published result. Source: arXiv:2610.25524 Section 4, p. 11

For σ in the standard simplex `stdSimplex ℝ (Fin n × Fin n)`, its second marginal `saddle_gap_second_marginal σ` in `stdSimplex ℝ (Fin n)` has j-th coordinate equal to the sum over i of σ(i, j).
-/

/-- For σ in `stdSimplex ℝ (Fin n × Fin n)`, its second marginal `saddle_gap_second_marginal σ` in `stdSimplex ℝ (Fin n)` has j-th coordinate equal to the sum over i of σ(i, j). -/
def saddle_gap_second_marginal {n : ℕ} (σ : stdSimplex ℝ (Fin n × Fin n)) : stdSimplex ℝ (Fin n) := ⟨fun j => ∑ i : Fin n, σ.val (i, j), by
    constructor
    · intro j
      exact Finset.sum_nonneg fun i _ => σ.property.1 (i, j)
    · rw [Finset.sum_comm, ← Finset.sum_product']
      exact σ.property.2⟩
