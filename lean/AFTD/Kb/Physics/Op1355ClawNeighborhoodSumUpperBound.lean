import AFTD.Prelude

/-!
# op_1355_claw_neighborhood_sum_upper_bound

Topic: statistical_mechanics   Node: f08af098fa5e

Provenance: helper lemma. OP-1355, explicit induced-claw witness for necessity

The closed-neighborhood activity sum at the center is at most 31+1/16 for the explicit embedded-claw profile.
-/

open scoped Classical BigOperators in
theorem op_1355_claw_neighborhood_sum_upper_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c u v w : V)
    (hadj : G.Adj c u ∧ G.Adj c v ∧ G.Adj c w)
    (hdist : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (hnon : ¬ G.Adj u v ∧ ¬ G.Adj u w ∧ ¬ G.Adj v w)
    (lam : V → ℝ)
    (hlam : ∀ x, lam x = if x = c then 1 else if x = u ∨ x = v ∨ x = w then 10 else 1 / (16 * (2 : ℝ) ^ Fintype.card V)) :
    (∑ x ∈ insert c (G.neighborFinset c), lam x) ≤ (31 : ℝ) + 1 / 16 := by
  classical
  set S := insert c (G.neighborFinset c) with hS
  set B : Finset V := {c, u, v, w} with hB
  have hcu : c ≠ u := hadj.1.ne
  have hcv : c ≠ v := hadj.2.1.ne
  have hcw : c ≠ w := hadj.2.2.ne
  have huc : u ≠ c := hadj.1.ne'
  have hvc : v ≠ c := hadj.2.1.ne'
  have hwc : w ≠ c := hadj.2.2.ne'
  have huv : u ≠ v := hdist.1
  have huw : u ≠ w := hdist.2.1
  have hvw : v ≠ w := hdist.2.2
  have hBsub : B ⊆ S := by
    intro x hx
    rw [hB] at hx
    rw [hS]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with hxc | hxu | hxv | hxw
    · exact Or.inl hxc
    · exact Or.inr (hxu.symm ▸ (SimpleGraph.mem_neighborFinset G c u).mpr hadj.1)
    · exact Or.inr (hxv.symm ▸ (SimpleGraph.mem_neighborFinset G c v).mpr hadj.2.1)
    · exact Or.inr (hxw.symm ▸ (SimpleGraph.mem_neighborFinset G c w).mpr hadj.2.2)
  have hlamc : lam c = 1 := by rw [hlam c]; simp
  have hlamu : lam u = 10 := by rw [hlam u]; simp [huc]
  have hlamv : lam v = 10 := by rw [hlam v]; simp [hvc]
  have hlamw : lam w = 10 := by rw [hlam w]; simp [hwc]
  have hsumB : ∑ x ∈ B, lam x = 31 := by
    rw [hB]
    rw [Finset.sum_insert (by simp [hcu, hcv, hcw])]
    rw [Finset.sum_insert (by simp [huv, huw])]
    rw [Finset.sum_insert (by simp [hvw])]
    rw [Finset.sum_singleton]
    rw [hlamc, hlamu, hlamv, hlamw]
    norm_num
  have hsmall : ∀ x ∈ S \ B, lam x = 1 / (16 * (2:ℝ) ^ Fintype.card V) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxS, hxB⟩ := hx
    rw [hB] at hxB
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxB
    obtain ⟨hxc, hxu, hxv, hxw⟩ := hxB
    rw [hlam x]
    simp [hxc, hxu, hxv, hxw]
  have hstep7 : ∑ x ∈ S \ B, lam x ≤ (Fintype.card V : ℝ) * (1 / (16 * (2:ℝ) ^ Fintype.card V)) := by
    have hcongr : ∑ x ∈ S \ B, lam x = ∑ x ∈ S \ B, (1 / (16 * (2:ℝ) ^ Fintype.card V)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hsmall x hx
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_univ (S \ B)
  have hfinal : (Fintype.card V : ℝ) * (1 / (16 * (2:ℝ) ^ Fintype.card V)) ≤ 1/16 := by
    have hnlt_nat : Fintype.card V ≤ 2 ^ Fintype.card V := (Nat.lt_two_pow_self).le
    have hnlt : (Fintype.card V : ℝ) ≤ (2:ℝ) ^ Fintype.card V := by
      have := Nat.cast_le (α := ℝ).mpr hnlt_nat
      rwa [Nat.cast_pow] at this
    have hpos : (0:ℝ) < 1 / (16 * (2:ℝ) ^ Fintype.card V) := by positivity
    calc (Fintype.card V : ℝ) * (1 / (16 * (2:ℝ) ^ Fintype.card V))
        ≤ (2:ℝ) ^ Fintype.card V * (1 / (16 * (2:ℝ) ^ Fintype.card V)) :=
          mul_le_mul_of_nonneg_right hnlt (le_of_lt hpos)
      _ = 1/16 := by field_simp
  calc ∑ x ∈ S, lam x
      = ∑ x ∈ S \ B, lam x + ∑ x ∈ B, lam x := (Finset.sum_sdiff hBsub).symm
    _ = ∑ x ∈ S \ B, lam x + 31 := by rw [hsumB]
    _ ≤ (Fintype.card V : ℝ) * (1 / (16 * (2:ℝ) ^ Fintype.card V)) + 31 := by linarith [hstep7]
    _ ≤ 1/16 + 31 := by linarith [hfinal]
    _ = 31 + 1/16 := by ring
