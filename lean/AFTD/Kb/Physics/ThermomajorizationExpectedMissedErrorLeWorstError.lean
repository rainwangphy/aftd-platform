import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationWitnessX
import AFTD.Kb.Physics.ThermomajorizationWitnessY
import AFTD.Kb.Physics.ThermomajorizationExpectedMissedError
import AFTD.Kb.Physics.ThermomajorizationRandomProbeWorstError
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.Physics.ThermomajorizationWitnessXMemAntitoneStdSimplex
import AFTD.Kb.Physics.ThermomajorizationWitnessYMemAntitoneStdSimplex
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Physics.ThermomajorizationDiff

/-!
# thermomajorization_expected_missed_error_le_worst_error

Topic: quantum_mechanics   Node: ebb5f9b60853

Provenance: helper lemma. OP-2138

For any dimension n, function q : Finset.Ioo 0 n → ℝ, and candidate parameters a < j < b ≤ n, the expected missed error thermomajorization_expected_missed_error n q (thermomajorization_witness_x n a j b) (thermomajorization_witness_y n j) is less than or equal to thermomajorization_random_probe_worst_error n q.
-/

lemma thermomajorization_expected_missed_error_le_worst_error_le_iSup_2
    {α β : Type*} (f : α → β → ℝ) (S : Set α) (T : Set β)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ a ∈ S, ∀ b ∈ T, f a b ≤ M)
    {x : α} (hx : x ∈ S) {y : β} (hy : y ∈ T) :
    f x y ≤ ⨆ a ∈ S, ⨆ b ∈ T, f a b := by
  have h4 : f x y ≤ ⨆ (_ : y ∈ T), f x y := by
    have hbdd : BddAbove (Set.range (fun (_ : y ∈ T) => f x y)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨hy', rfl⟩
      exact hM x hx y hy'
    exact le_ciSup hbdd hy
  have h3 : (⨆ (_ : y ∈ T), f x y) ≤ ⨆ b, ⨆ (_ : b ∈ T), f x b := by
    have hbdd : BddAbove (Set.range (fun b => ⨆ (_ : b ∈ T), f x b)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨b, rfl⟩
      refine Real.iSup_le (fun hb => hM x hx b hb) hM0
    exact le_ciSup hbdd y
  have h2 : (⨆ b, ⨆ (_ : b ∈ T), f x b) ≤ ⨆ (_ : x ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f x b := by
    have hbdd : BddAbove (Set.range (fun (_ : x ∈ S) => ⨆ b, ⨆ (_ : b ∈ T), f x b)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨hx', rfl⟩
      refine Real.iSup_le (fun b => ?_) hM0
      refine Real.iSup_le (fun hb => hM x hx b hb) hM0
    exact le_ciSup hbdd hx
  have h1 : (⨆ (_ : x ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f x b) ≤
      ⨆ a, ⨆ (_ : a ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f a b := by
    have hbdd : BddAbove (Set.range (fun a => ⨆ (_ : a ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f a b)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨a, rfl⟩
      refine Real.iSup_le (fun ha => ?_) hM0
      refine Real.iSup_le (fun b => ?_) hM0
      refine Real.iSup_le (fun hb => hM a ha b hb) hM0
    exact le_ciSup hbdd x
  exact h4.trans (h3.trans (h2.trans h1))

/-- Expected missed error at any candidate witness pair is bounded by the worst-case error. -/
theorem thermomajorization_expected_missed_error_le_worst_error (n : ℕ)
    (q : Finset.Ioo 0 n → ℝ) (a j b : ℕ)
    (ha : a < j) (hj : j < b) (hb : b ≤ n) :
    thermomajorization_expected_missed_error n q
      (thermomajorization_witness_x n a j b) (thermomajorization_witness_y n j) ≤
    thermomajorization_random_probe_worst_error n q := by
  have hj0 : 0 < j := (Nat.zero_le a).trans_lt ha
  have hjn : j ≤ n := hj.le.trans hb
  have hx_mem : thermomajorization_witness_x n a j b ∈
      {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v} :=
    thermomajorization_witness_x_mem_antitone_stdSimplex n a j b ha hj hb
  have hy_mem : thermomajorization_witness_y n j ∈
      {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v} :=
    thermomajorization_witness_y_mem_antitone_stdSimplex n j hj0 hjn

  let M : ℝ := 1 + ∑ k : Finset.Ioo 0 n, |q k|
  have hM0 : 0 ≤ M := by positivity

  have hM : ∀ u ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v},
            ∀ v ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v},
            thermomajorization_expected_missed_error n q u v ≤ M := by
    rintro u ⟨hu, -⟩ v ⟨hv, -⟩
    have h_diff : ∀ k : ℕ, thermomajorization_diff u v k ≤ 1 := by
      intro k
      unfold thermomajorization_diff
      have h1 : (Finset.filter (fun (i : Fin n) => (i.val < k)) Finset.univ).sum (fun i => v i - u i) ≤
                (Finset.filter (fun (i : Fin n) => (i.val < k)) Finset.univ).sum (fun i => v i) := by
        apply Finset.sum_le_sum
        intro i _
        have : 0 ≤ u i := hu.1 i
        linarith
      have h2 : (Finset.filter (fun (i : Fin n) => (i.val < k)) Finset.univ).sum (fun i => v i) ≤
                Finset.univ.sum (fun i => v i) := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro i
        exact hv.1 i
      have h3 : Finset.univ.sum (fun i => v i) = 1 := hv.2
      linarith
    have h_probe : thermomajorization_probe_error n (Finset.Ioo 0 n) u v ≤ 1 := by
      dsimp [thermomajorization_probe_error]
      rw [Finset.max'_le_iff]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_image] at hz
      rcases hz with rfl | ⟨k, hk, rfl⟩
      · linarith
      · exact h_diff k
    have h_term : ∀ k : Finset.Ioo 0 n, - (q k * max 0 (thermomajorization_diff u v (k : ℕ))) ≤ |q k| := by
      intro k
      have hd := h_diff (k : ℕ)
      have h1 : 0 ≤ max 0 (thermomajorization_diff u v (k : ℕ)) := le_max_left 0 _
      have h2 : max 0 (thermomajorization_diff u v (k : ℕ)) ≤ 1 := by
        rw [max_le_iff]
        exact ⟨zero_le_one, hd⟩
      have h3 : - (q k * max 0 (thermomajorization_diff u v (k : ℕ))) ≤
                |- (q k * max 0 (thermomajorization_diff u v (k : ℕ)))| := le_abs_self _
      rw [abs_neg, abs_mul, abs_of_nonneg h1] at h3
      have h4 : |q k| * max 0 (thermomajorization_diff u v (k : ℕ)) ≤ |q k| * 1 :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg (q k))
      rw [mul_one] at h4
      linarith
    have h_sum : - ∑ k : Finset.Ioo 0 n, q k * max 0 (thermomajorization_diff u v (k : ℕ)) ≤
                 ∑ k : Finset.Ioo 0 n, |q k| := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro k _
      exact h_term k
    unfold thermomajorization_expected_missed_error
    linarith

  exact thermomajorization_expected_missed_error_le_worst_error_le_iSup_2
    (thermomajorization_expected_missed_error n q)
    {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}
    {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}
    M hM0 hM hx_mem hy_mem
