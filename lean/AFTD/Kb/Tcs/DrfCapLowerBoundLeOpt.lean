import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance
import AFTD.Kb.Tcs.MultidimOpt
import AFTD.Kb.Tcs.MultidimIsFeasibleSchedule

/-!
# drf_cap_lower_bound_le_opt

Topic: online_algorithms   Node: 2b8b322671ad

Provenance: formalization of a published result. Source: arXiv:2611.07905 Section 3.1.2

For every multidimensional scheduling instance I with D resources and zero release times, the sum over all jobs of processing requirement divided by rate cap, ∑ j, I.p j / I.u j, is at most the offline optimal total completion time multidim_opt I.
-/

/-- The sum over jobs of processing requirement divided by rate cap is at most the offline optimal total completion time. -/
theorem drf_cap_lower_bound_le_opt {D : ℕ} (I : MultidimInstance D) :
    (∑ j : Fin I.n, I.p j / I.u j) ≤ multidim_opt I := by
  unfold multidim_opt
  apply le_csInf
  · -- the set of achievable total completion times is nonempty
    set c : ℝ := 1 / ((I.n : ℝ) + 1) with hc_def
    have hcpos : 0 < c := by positivity
    have hnc : (I.n : ℝ) * c ≤ 1 := by
      rw [hc_def, mul_one_div, div_le_one (by positivity)]
      linarith
    refine ⟨∑ j, I.p j / min (I.u j) c, fun j _ => min (I.u j) c, fun j => I.p j / min (I.u j) c,
      ⟨?_, ?_, ?_⟩, rfl⟩
    · intro j t
      exact ⟨le_min (le_of_lt (I.hu j)) (le_of_lt hcpos), min_le_left _ _⟩
    · intro d t ht
      have h : ∀ j : Fin I.n, I.a j d * min (I.u j) c ≤ c := by
        intro j
        calc I.a j d * min (I.u j) c ≤ 1 * min (I.u j) c :=
              mul_le_mul_of_nonneg_right (I.ha_le_one j d) (le_of_lt (lt_min (I.hu j) hcpos))
          _ = min (I.u j) c := one_mul _
          _ ≤ c := min_le_right _ _
      calc ∑ j, I.a j d * min (I.u j) c ≤ ∑ _j : Fin I.n, c := Finset.sum_le_sum (fun j _ => h j)
        _ = (I.n : ℝ) * c := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ 1 := hnc
    · intro j
      have hpos : 0 < min (I.u j) c := lt_min (I.hu j) hcpos
      exact ⟨le_of_lt (div_pos (I.hp j) hpos), intervalIntegrable_const, by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        exact div_mul_cancel₀ _ (ne_of_gt hpos)⟩
  · -- every achievable total completion time dominates ∑ p_j/u_j
    intro b hb
    obtain ⟨x, C, ⟨hx, hR, hC⟩, rfl⟩ := hb
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨hCj0, hint, hval⟩ := hC j
    have hmono : ∫ (t : ℝ) in 0..C j, x j t ≤ ∫ (t : ℝ) in 0..C j, I.u j := by
      refine intervalIntegral.integral_mono_on hCj0 hint intervalIntegrable_const ?_
      intro t ht
      exact (hx j t).2
    rw [intervalIntegral.integral_const] at hmono
    have hle : I.p j ≤ I.u j * C j := by
      rw [← hval]
      simpa [smul_eq_mul, mul_comm] using hmono
    rw [div_le_iff₀ (I.hu j)]
    linarith
