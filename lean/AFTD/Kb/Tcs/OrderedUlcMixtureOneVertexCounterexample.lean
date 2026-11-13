import AFTD.Prelude
import AFTD.Kb.Tcs.SequenceUlcBoundedMixture

/-!
# ordered_ulc_mixture_one_vertex_counterexample

Topic: combinatorics   Node: 315e375a86ad

Provenance: helper lemma. An explicit rescaling of the construction in arXiv:0707.2340, Section 7, Counterexample 1, used to eliminate an analytic route to OP-1399.

Even with the normalized initial terms and the exact rank-one count of a 24-vertex tree, ordered bounded-mixture ultra-log-concavity can fail after a one-vertex extension.
-/

noncomputable section
private def mix_counterexample_pa (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 24 else if k = 2 then 29233 / 480
  else if k = 3 then 253 / 120 else if k = 4 then 5313 / 102400
  else if k = 5 then 1771 / 1310720000 else 0
private def mix_counterexample_pu (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 24 else if k = 2 then 92
  else if k = 3 then 2024 / 9 else if k = 4 then 1771 / 160
  else if k = 5 then 5098709 / 12288000 else 0
private def mix_counterexample_pc (k : ℕ) : ℝ := mix_counterexample_pu k - mix_counterexample_pa k

private theorem mix_counterexample_pa_zero (k : ℕ) (h : 5 < k) : mix_counterexample_pa k = 0 := by
  simp [mix_counterexample_pa, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega,
    show k ≠ 3 by omega, show k ≠ 4 by omega, show k ≠ 5 by omega]
private theorem mix_counterexample_pu_zero (k : ℕ) (h : 5 < k) : mix_counterexample_pu k = 0 := by
  simp [mix_counterexample_pu, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega,
    show k ≠ 3 by omega, show k ≠ 4 by omega, show k ≠ 5 by omega]
private theorem mix_counterexample_pa_pos (k : ℕ) (h : k ≤ 5) : 0 < mix_counterexample_pa k := by
  interval_cases k <;> norm_num [mix_counterexample_pa]
private theorem mix_counterexample_pu_pos (k : ℕ) (h : k ≤ 5) : 0 < mix_counterexample_pu k := by
  interval_cases k <;> norm_num [mix_counterexample_pu]

private theorem mix_counterexample_input_valid : sequence_ulc_bounded_mixture 24 mix_counterexample_pa mix_counterexample_pc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [mix_counterexample_pa]
  · norm_num [mix_counterexample_pc, mix_counterexample_pu, mix_counterexample_pa]
  · intro k
    by_cases hk : k ≤ 5
    · interval_cases k <;> norm_num [mix_counterexample_pa, mix_counterexample_pc, mix_counterexample_pu, Nat.choose]
    · have h : 5 < k := by omega
      simp [mix_counterexample_pc, mix_counterexample_pa_zero k h, mix_counterexample_pu_zero k h]
  · intro k hk
    have h : 5 < k := by omega
    simp [mix_counterexample_pc, mix_counterexample_pa_zero k h, mix_counterexample_pu_zero k h]
  · intro i j hij hj
    by_cases hi : i ≤ 5
    · exact mix_counterexample_pa_pos i hi
    · have hz := mix_counterexample_pa_zero j (by omega)
      rw [hz] at hj
      norm_num at hj
  · intro i j hij hj
    have huj : 0 < mix_counterexample_pu j := by simpa [mix_counterexample_pc] using hj
    have hui : 0 < mix_counterexample_pu i := by
      by_cases hi : i ≤ 5
      · exact mix_counterexample_pu_pos i hi
      · have hz := mix_counterexample_pu_zero j (by omega)
        rw [hz] at huj
        norm_num at huj
    simpa [mix_counterexample_pc] using hui
  · intro i j hij
    by_cases hj : j ≤ 5
    · have hi : i ≤ 5 := by omega
      interval_cases i <;> interval_cases j <;> norm_num [mix_counterexample_pa, mix_counterexample_pc, mix_counterexample_pu] at *
    · have hj' : 5 < j := by omega
      simp [mix_counterexample_pc, mix_counterexample_pa_zero j hj', mix_counterexample_pu_zero j hj']
  · intro t ht0 ht1 k hk
    by_cases hk3 : k ≤ 3
    · interval_cases k <;> norm_num [mix_counterexample_pa, mix_counterexample_pc, mix_counterexample_pu, Nat.choose] <;>
        nlinarith [sq_nonneg t, sq_nonneg (1 - t), mul_nonneg ht0 (show 0 ≤ 1 - t by linarith)]
    · have hk6 : 5 < k + 2 := by omega
      have hc0 : mix_counterexample_pc (k + 2) = 0 := by
        simp only [mix_counterexample_pc, mix_counterexample_pa_zero (k + 2) hk6, mix_counterexample_pu_zero (k + 2) hk6, sub_self]
      rw [mix_counterexample_pa_zero (k + 2) hk6, hc0]
      simp only [mul_zero, add_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

private def mix_counterexample_pg (k : ℕ) : ℝ := mix_counterexample_pu k + if k = 0 then 0 else mix_counterexample_pa (k - 1)
private def mix_counterexample_pe (k : ℕ) : ℝ := if k = 0 then 0 else mix_counterexample_pc (k - 1)
end

theorem ordered_ulc_mixture_one_vertex_counterexample : ∃ a c : ℕ → ℝ, a 1 + c 1 = 24 ∧ sequence_ulc_bounded_mixture 24 a c ∧
    ¬ sequence_ulc_bounded_mixture 25
      (fun k => a k + c k + if k = 0 then 0 else a (k - 1))
      (fun k => if k = 0 then 0 else c (k - 1)) := by
  refine ⟨mix_counterexample_pa, mix_counterexample_pc, by norm_num [mix_counterexample_pa, mix_counterexample_pc, mix_counterexample_pu], mix_counterexample_input_valid, ?_⟩
  have hg : (fun k => mix_counterexample_pa k + mix_counterexample_pc k + if k = 0 then 0 else mix_counterexample_pa (k - 1)) = mix_counterexample_pg := by
    funext k
    simp only [mix_counterexample_pc, mix_counterexample_pg]
    ring
  have he : (fun k => if k = 0 then 0 else mix_counterexample_pc (k - 1)) = mix_counterexample_pe := rfl
  rw [hg, he]
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, hmix⟩
  have hx := hmix 0 (by norm_num) (by norm_num) 3 (by norm_num)
  norm_num [mix_counterexample_pg, mix_counterexample_pe, mix_counterexample_pa, mix_counterexample_pu, mix_counterexample_pc, Nat.choose] at hx
