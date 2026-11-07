import AFTD.Prelude
import AFTD.Kb.Tcs.IsCommutingQuantum
import AFTD.Kb.Tcs.IsAlmostQuantum

/-!
# is_almost_quantum_of_is_commuting_quantum

Topic: communication   Node: 6a690383c694

Provenance: helper lemma. arXiv:2610.41448, An Unbounded Separation of Almost-Quantum and Commuting-Operator Correlations in Zero-Error Communication, Eq. (2)

Every commuting-operator quantum correlation is almost-quantum: if p satisfies is_commuting_quantum p, then p satisfies is_almost_quantum p.
-/

/-- Every commuting-operator quantum correlation is almost-quantum. -/
theorem is_almost_quantum_of_is_commuting_quantum {X Y A B : Type*} [Fintype A] [Fintype B]
    {p : X → Y → A → B → ℝ} (h : is_commuting_quantum p) :
    is_almost_quantum p := by
  obtain ⟨E, x, x1, hcs, ψ, hψ, A_meas, hA, B_meas, hB, hcomm, hp⟩ := h
  exact ⟨E, x, x1, hcs, ψ, hψ, A_meas, hA, B_meas, hB,
    fun x y a b => hcomm x y a b ψ, hp⟩
