import AFTD.Prelude
import AFTD.Kb.Physics.TwoQubitCandidateFidelityBound
import AFTD.Kb.Physics.BinaryEntropyNats

/-!
# two_qubit_candidate_fidelity_bound_at_zero

Topic: quantum_mechanics   Node: 60ec5452203b

Provenance: formalization of a published result. Source: OP-1552; arXiv:2409.01966

At adjusted entropy deficit ε = 0, the candidate fidelity bound equals 1.
-/

lemma two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_eq (x : ℝ) :
    binary_entropy_nats x = Real.binEntropy x := by
  rw [binary_entropy_nats, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

lemma two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_one :
    binary_entropy_nats 1 = 0 := by
  rw [two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_eq, Real.binEntropy_one]

lemma two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_half :
    binary_entropy_nats (1 / 2) = Real.log 2 := by
  rw [two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_eq]
  have h : (1 : ℝ) / 2 = 2⁻¹ := by norm_num
  rw [h, Real.binEntropy_two_inv]

/-- At zero deficit epsilon = 0, the candidate fidelity bound achieves the maximally entangled Bell state fidelity of 1. -/
theorem two_qubit_candidate_fidelity_bound_at_zero :
    two_qubit_candidate_fidelity_bound 0 = 1 := by
  unfold two_qubit_candidate_fidelity_bound
  have hS : { F : ℝ | ∃ p q : ℝ,
      0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 ∧
      Real.log 2 + binary_entropy_nats p - binary_entropy_nats (p * q) ≤ 0 ∧
      F = max (p * (1 + 2 * Real.sqrt (q * (1 - q))) / 2) ((1 - p) / 2) } = {1} := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, q, hp0, hp1, -, -, h_entropy, rfl⟩
      rw [two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_eq,
          two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_eq] at h_entropy
      have hp_nonneg : 0 ≤ Real.binEntropy p := Real.binEntropy_nonneg hp0 hp1
      have hpq_le : Real.binEntropy (p * q) ≤ Real.log 2 := Real.binEntropy_le_log_two
      have h_eq : Real.binEntropy p = 0 ∧ Real.binEntropy (p * q) = Real.log 2 := by
        constructor <;> linarith
      have hp_cases : p = 0 ∨ p = 1 := Real.binEntropy_eq_zero.mp h_eq.1
      have hpq_eq : p * q = 2⁻¹ := Real.binEntropy_eq_log_two.mp h_eq.2
      cases hp_cases with
      | inl hp0' =>
        subst hp0'
        simp only [zero_mul] at hpq_eq
        have : (0 : ℝ) ≠ 2⁻¹ := by norm_num
        contradiction
      | inr hp1' =>
        subst hp1'
        simp only [one_mul] at hpq_eq
        have hq : q = 1 / 2 := by linarith
        subst hq
        have hs : (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 := by ring
        rw [hs, Real.sqrt_sq (by norm_num)]
        norm_num
    · rintro rfl
      refine ⟨1, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
      · rw [one_mul, two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_one,
            two_qubit_candidate_fidelity_bound_at_zero_entropy_nats_half]
        linarith
      · have hs : (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 := by ring
        rw [hs, Real.sqrt_sq (by norm_num)]
        norm_num
  rw [hS]
  exact csInf_singleton 1
