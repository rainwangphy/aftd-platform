import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationMinimaxError
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.ThermomajorizationMissedError
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# thermomajorization_full_budget_zero_error

Topic: quantum_mechanics   Node: 57f5c4273108

Provenance: formalization of a published result. Source: arXiv:2610.35433, Corollary 2

For any natural number n with 1 ≤ n, measuring all n - 1 binary probes gives zero minimax missed error: thermomajorization_minimax_error n (n - 1) = 0.
-/

/-- Full probe budget of n - 1 ranks achieves zero missed thermomajorization error. -/
theorem thermomajorization_full_budget_zero_error (n : ℕ) (hn : 1 ≤ n) : thermomajorization_minimax_error n (n - 1) = 0 := by
  have hmiss : thermomajorization_missed_error n (Finset.Ioo 0 n) = 0 := by
    unfold thermomajorization_missed_error
    simp only [sub_self]
    simp
  unfold thermomajorization_minimax_error
  have hcard : (Finset.Ioo 0 n).card = n - 1 := by simp
  rw [← hcard, Finset.powersetCard_self]
  simp only [Finset.mem_singleton]
  have key : ∀ F, (⨅ (_ : F = Finset.Ioo 0 n), thermomajorization_missed_error n F) = 0 := by
    intro F
    by_cases hF : F = Finset.Ioo 0 n
    · subst hF
      rw [ciInf_subsingleton rfl]
      exact hmiss
    · haveI : IsEmpty (F = Finset.Ioo 0 n) := ⟨fun h => hF h⟩
      rw [iInf_of_isEmpty]
      exact Real.sInf_empty
  simp_rw [key]
  exact ciInf_const
