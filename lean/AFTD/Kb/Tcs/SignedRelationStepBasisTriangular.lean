import AFTD.Prelude
import AFTD.Kb.Tcs.SignedRelation
import AFTD.Kb.Tcs.DualCertPBounds
import AFTD.Kb.Tcs.TriangularNumber
import AFTD.Kb.Tcs.DualCertP

/-!
# signed_relation_step_basis_triangular

Topic: combinatorics   Node: f9c85ef3d232

Provenance: helper lemma. step towards dual_certificate_identity

The evaluation of signed_relation n (j.val + 1) on the step basis vector v^(i) (1 if i <= k else 0) is 0 for i < j, 1 for i = j, and nonpositive (<= 0) for j < i. This is Step 1 (triangularity) of arXiv:2611.17360 Theorem 3.2.
-/

namespace DCB2

noncomputable def cs (n i t : ℕ) : ℝ := if 0 < t ∧ t ≤ n then (if i ≤ t - 1 then 1 else 0) else 0

theorem cs_nonneg (n i t : ℕ) : 0 ≤ cs n i t := by
  unfold cs; split_ifs <;> norm_num

theorem cs_mono {n i a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n) : cs n i a ≤ cs n i b := by
  unfold cs; split_ifs <;> first | (exfalso; omega) | norm_num

theorem sr_step (n J i : ℕ) :
    signed_relation n J (fun k : Fin n => if i ≤ k.val then 1 else 0) =
      (∑ t ∈ Finset.range (dual_cert_p (n - J + 1)), cs n i (J + t)) - cs n i (J - 1)
        - ∑ k ∈ Finset.range (dual_cert_p (n - J + 1) - 1), cs n i (n - triangular_number k) := by
  unfold signed_relation cs
  rfl

theorem step_triangular (n : ℕ) (hn : 1 ≤ n) (j i : Fin n) :
    let v : Fin n → ℝ := fun k => if i.val ≤ k.val then 1 else 0
    (i.val < j.val → signed_relation n (j.val + 1) v = 0) ∧
    (i.val = j.val → signed_relation n (j.val + 1) v = 1) ∧
    (j.val < i.val → signed_relation n (j.val + 1) v ≤ 0) := by
  intro v
  have hj := j.isLt
  have hi := i.isLt
  have hm : n - (j.val + 1) + 1 = n - j.val := by omega
  simp only [v, sr_step, hm]
  obtain ⟨hp1, hpm, hpT⟩ := dual_cert_p_bounds (n - j.val) (by omega)
  set p := dual_cert_p (n - j.val) with hp
  have hT : ∀ k < p - 1, j.val + p + 1 ≤ n - triangular_number k ∧ triangular_number k < n := by
    intro k hk
    have := hpT (by omega) k hk
    omega
  have hblock1 : i.val ≤ j.val → ∀ t ∈ Finset.range p, cs n i.val (j.val + 1 + t) = 1 := by
    intro hij t ht
    rw [Finset.mem_range] at ht
    unfold cs; rw [if_pos (by omega), if_pos (by omega)]
  have hminus1 : i.val ≤ j.val → ∀ k ∈ Finset.range (p - 1), cs n i.val (n - triangular_number k) = 1 := by
    intro hij k hk
    rw [Finset.mem_range] at hk
    have := hT k hk
    unfold cs; rw [if_pos (by omega), if_pos (by omega)]
  refine ⟨fun hij => ?_, fun hij => ?_, fun hij => ?_⟩
  · rw [Finset.sum_congr rfl (hblock1 hij.le), Finset.sum_congr rfl (hminus1 hij.le)]
    have hc : cs n i.val (j.val + 1 - 1) = 1 := by
      unfold cs; rw [if_pos (by omega), if_pos (by omega)]
    rw [hc]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hp1]; ring
  · rw [Finset.sum_congr rfl (hblock1 hij.le), Finset.sum_congr rfl (hminus1 hij.le)]
    have hc : cs n i.val (j.val + 1 - 1) = 0 := by
      unfold cs; split_ifs <;> first | rfl | omega
    rw [hc]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hp1]; ring
  · obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [hq, Finset.sum_range_succ', Nat.add_sub_cancel]
    have h0 : cs n i.val (j.val + 1 + 0) = 0 := by
      unfold cs; split_ifs <;> first | rfl | omega
    rw [h0, add_zero]
    have hle : ∑ t ∈ Finset.range q, cs n i.val (j.val + 1 + (t + 1)) ≤
        ∑ k ∈ Finset.range q, cs n i.val (n - triangular_number k) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.mem_range] at ht
      have := hT t (by omega)
      exact cs_mono (by omega) (by omega) (by omega)
    have := cs_nonneg n i.val j.val
    rw [show q + 1 - 1 = q by omega] at *

    linarith

end DCB2

/-- Evaluation of signed_relation on step basis vectors is 0 for i < j, 1 for i = j, and nonpositive for j < i. This is Step 1 of arXiv:2611.17360 Theorem 3.2. -/
theorem signed_relation_step_basis_triangular (n : ℕ) (hn : 1 ≤ n) (j i : Fin n) :
    let v : Fin n → ℝ := fun k => if i.val ≤ k.val then 1 else 0
    (i.val < j.val → signed_relation n (j.val + 1) v = 0) ∧
    (i.val = j.val → signed_relation n (j.val + 1) v = 1) ∧
    (j.val < i.val → signed_relation n (j.val + 1) v ≤ 0) := by
  exact DCB2.step_triangular n hn j i
