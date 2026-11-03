import AFTD.Prelude
import AFTD.Kb.Tcs.IsAlmostQuantum

/-!
# almost_quantum_efficiency

Topic: quantum   Node: 981153222b26

Provenance: formalization of a published result. Source: arXiv:2610.41448 Definition 2

The optimal zero-error conclusive efficiency η_AQ(N) of one-bit communication deciding equality of two labels in {1, ..., N} using almost-quantum correlations, defined as the supremum over zero-error almost-quantum protocols of the worst-case conclusive probability.
-/

/-- The optimal zero-error conclusive efficiency of one-bit communication for equality over almost-quantum correlations. -/
noncomputable def almost_quantum_efficiency (N : ℕ) : ℝ := sSup { c : ℝ | ∃ (p : Fin N → (Fin N × Fin 2) → Fin 2 → Option Bool → ℝ),
    is_almost_quantum p ∧
    (∀ s t : Fin N, if s = t then (∑ a : Fin 2, p s (t, a) a (some false)) = 0
                    else (∑ a : Fin 2, p s (t, a) a (some true)) = 0) ∧
    ∀ s t : Fin N, c ≤ ∑ a : Fin 2, p s (t, a) a (some (s = t)) }
