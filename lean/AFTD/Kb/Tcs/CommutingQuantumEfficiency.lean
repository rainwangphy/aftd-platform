import AFTD.Prelude
import AFTD.Kb.Tcs.IsCommutingQuantum

/-!
# commuting_quantum_efficiency

Topic: communication   Node: cff575b7900f

Provenance: formalization of a published result. Source: arXiv:2610.41448, An Unbounded Separation of Almost-Quantum and Commuting-Operator Correlations in Zero-Error Communication, Sec. 8

For integers K and N, the optimal zero-error conclusive efficiency η^{(K)}_{C_qc}(N) is the supremum over all zero-error commuting-operator quantum protocols with K messages of the worst-case conclusive probability for deciding equality of two labels in {1, ..., N}.
-/

/-- Optimal worst-case conclusive efficiency for certifying equality with K messages over commuting-operator quantum correlations. -/
noncomputable def commuting_quantum_efficiency (K N : ℕ) : ℝ :=
  sSup {c | ∃ (p : Fin N → Fin N × Fin K → Fin K → Option Bool → ℝ),
    is_commuting_quantum p ∧
    (∀ (s t : Fin N), if s = t then ∑ a, p s (t, a) a (some false) = 0 else ∑ a, p s (t, a) a (some true) = 0) ∧
    ∀ (s t : Fin N), c ≤ ∑ a, p s (t, a) a (some (decide (s = t)))}
