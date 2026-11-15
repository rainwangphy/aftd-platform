import AFTD.Prelude

/-!
# op_1355_claw_center_partition_upper_bound

Topic: statistical_mechanics   Node: 17508e0de8ed

Provenance: helper lemma. OP-1355, explicit induced-claw witness for necessity

The total weight of independent sets containing the center is at most 17/16 for the explicit embedded-claw activity profile.
-/

open scoped Classical BigOperators in
theorem op_1355_claw_center_partition_upper_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c u v w : V)
    (hadj : G.Adj c u ∧ G.Adj c v ∧ G.Adj c w)
    (hdist : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (hnon : ¬ G.Adj u v ∧ ¬ G.Adj u w ∧ ¬ G.Adj v w)
    (lam : V → ℝ)
    (hlam : ∀ x, lam x = if x = c then 1 else if x = u ∨ x = v ∨ x = w then 10 else 1 / (16 * (2 : ℝ) ^ Fintype.card V)) :
    (∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V) ∧ c ∈ I), ∏ x ∈ I, lam x) ≤ (17 : ℝ) / 16 := by
  classical
  let eps : ℝ := 1 / (16 * (2 : ℝ) ^ Fintype.card V)
  have heps_pos : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_le_one : eps ≤ 1 := by
    dsimp [eps]
    rw [div_le_one (by positivity)]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ Fintype.card V := one_le_pow₀ (by norm_num)
    nlinarith
  have hlam_c : lam c = 1 := by
    rw [hlam c]
    simp
  have hlam_eps : ∀ x, x ≠ c → x ≠ u → x ≠ v → x ≠ w → lam x = eps := by
    intro x hxc hxu hxv hxw
    rw [hlam x]
    simp [hxc, hxu, hxv, hxw, eps]
  have hlam_nonneg : ∀ x, 0 ≤ lam x := by
    intro x
    rw [hlam x]
    split_ifs with h1 h2
    · norm_num
    · norm_num
    · exact heps_pos.le
  have hlam_le_one : ∀ {I : Finset V}, G.IsIndepSet (I : Set V) → c ∈ I → ∀ x ∈ I, lam x ≤ 1 := by
    intro I hInd hc x hx
    by_cases hxc : x = c
    · subst hxc
      exact hlam_c.le
    · have hxu : x ≠ u := by
        intro h
        subst h
        exact (hInd hc hx (Ne.symm hxc)) hadj.1
      have hxv : x ≠ v := by
        intro h
        subst h
        exact (hInd hc hx (Ne.symm hxc)) hadj.2.1
      have hxw : x ≠ w := by
        intro h
        subst h
        exact (hInd hc hx (Ne.symm hxc)) hadj.2.2
      rw [hlam_eps x hxc hxu hxv hxw]
      exact heps_le_one
  let T : Finset (Finset V) := Finset.univ.filter (fun I : Finset V => G.IsIndepSet (I : Set V) ∧ c ∈ I)
  change (∑ I ∈ T, (∏ x ∈ I, lam x)) ≤ (17 : ℝ) / 16
  have hsingle_mem : ({c} : Finset V) ∈ T := by
    dsimp [T]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro x hx y hy hxy
      simp at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · simp
  have hbound : ∀ I ∈ T, I ≠ {c} → (∏ x ∈ I, lam x) ≤ eps := by
    intro I hI hne
    dsimp [T] at hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
    obtain ⟨hInd, hc⟩ := hI
    have hx_exists : ∃ x ∈ I, x ≠ c := by
      by_contra h
      have h' : ∀ x ∈ I, x = c := by
        intro x hx
        by_contra hxnc
        exact h ⟨x, hx, hxnc⟩
      have h_eq : I = {c} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        exact ⟨hc, h'⟩
      exact hne h_eq
    obtain ⟨x, hxI, hxc⟩ := hx_exists
    have hxu : x ≠ u := by
      intro h
      subst h
      exact (hInd hc hxI (Ne.symm hxc)) hadj.1
    have hxv : x ≠ v := by
      intro h
      subst h
      exact (hInd hc hxI (Ne.symm hxc)) hadj.2.1
    have hxw : x ≠ w := by
      intro h
      subst h
      exact (hInd hc hxI (Ne.symm hxc)) hadj.2.2
    have hxlam : lam x = eps := hlam_eps x hxc hxu hxv hxw
    have hprod_le : (∏ y ∈ I.erase x, lam y) ≤ 1 := by
      apply Finset.prod_le_one
      · intro y _
        exact hlam_nonneg y
      · intro y hy
        exact hlam_le_one hInd hc y (Finset.mem_of_mem_erase hy)
    calc
      ∏ y ∈ I, lam y = lam x * ∏ y ∈ I.erase x, lam y := by
        rw [Finset.mul_prod_erase I lam hxI]
      _ ≤ lam x * 1 := by
        apply mul_le_mul_of_nonneg_left hprod_le
        rw [hxlam]
        exact heps_pos.le
      _ = eps := by
        rw [hxlam]
        ring
  have hsplit : ∑ I ∈ T, (∏ x ∈ I, lam x) = 1 + ∑ I ∈ T.erase {c}, (∏ x ∈ I, lam x) := by
    rw [← Finset.add_sum_erase T (fun I => ∏ x ∈ I, lam x) hsingle_mem]
    congr 1
    rw [Finset.prod_singleton, hlam_c]
  have hrest : ∑ I ∈ T.erase {c}, (∏ x ∈ I, lam x) ≤ (1 : ℝ) / 16 := by
    have h1 : ∑ I ∈ T.erase {c}, (∏ x ∈ I, lam x) ≤ ∑ I ∈ T.erase {c}, eps := by
      apply Finset.sum_le_sum
      intro I hI
      have hI' : I ∈ T := (Finset.mem_erase.mp hI).2
      have hne : I ≠ {c} := (Finset.mem_erase.mp hI).1
      exact hbound I hI' hne
    have h2 : ∑ I ∈ T.erase {c}, eps = eps * ((T.erase {c}).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hcard : ((T.erase {c}).card : ℝ) ≤ (2 : ℝ) ^ Fintype.card V := by
      have h := Finset.card_le_univ (T.erase {c})
      rw [Fintype.card_finset] at h
      exact_mod_cast h
    have h3 : eps * ((T.erase {c}).card : ℝ) ≤ eps * (2 : ℝ) ^ Fintype.card V :=
      mul_le_mul_of_nonneg_left hcard heps_pos.le
    have h4 : eps * (2 : ℝ) ^ Fintype.card V = (1 : ℝ) / 16 := by
      dsimp [eps]
      field_simp
    calc
      ∑ I ∈ T.erase {c}, (∏ x ∈ I, lam x) ≤ ∑ I ∈ T.erase {c}, eps := h1
      _ = eps * ((T.erase {c}).card : ℝ) := h2
      _ ≤ eps * (2 : ℝ) ^ Fintype.card V := h3
      _ = (1 : ℝ) / 16 := h4
  calc
    ∑ I ∈ T, (∏ x ∈ I, lam x) = 1 + ∑ I ∈ T.erase {c}, (∏ x ∈ I, lam x) := hsplit
    _ ≤ 1 + (1 : ℝ) / 16 := by linarith [hrest]
    _ = (17 : ℝ) / 16 := by norm_num
