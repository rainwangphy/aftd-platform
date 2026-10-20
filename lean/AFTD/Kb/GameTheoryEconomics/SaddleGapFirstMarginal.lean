import AFTD.Prelude

/-!
# saddle_gap_first_marginal

Topic: equilibria   Node: 4ab7c6390ebb

Provenance: formalization of a published result. Source: arXiv:2610.25524 Section 4

For σ in the standard simplex `stdSimplex ℝ (Fin n × Fin n)`, its first marginal `saddle_gap_first_marginal σ` in `stdSimplex ℝ (Fin n)` has i-th coordinate equal to the sum over j of σ(i, j).
-/

/-- First marginal distribution of a joint strategy σ on Fin n × Fin n. -/
def saddle_gap_first_marginal {n : ℕ} (σ : stdSimplex ℝ (Fin n × Fin n)) : stdSimplex ℝ (Fin n) := ⟨fun i => ∑ j : Fin n, σ.val (i, j), by
  constructor
  · intro i
    exact Finset.sum_nonneg fun j _ => σ.property.1 (i, j)
  · rw [← Finset.sum_product']
    exact σ.property.2⟩
