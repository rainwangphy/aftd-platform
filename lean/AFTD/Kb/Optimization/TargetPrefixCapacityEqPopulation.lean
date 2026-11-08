import AFTD.Prelude
import AFTD.Kb.Optimization.PopulationCapacity
import AFTD.Kb.Optimization.ThermomajorizationPrefix
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Optimization.ThermallyReachableMicro
import AFTD.Kb.Optimization.BlockPopulationCapacity
import AFTD.Kb.Optimization.ThermallyReachableBlockPopulations
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Optimization.FiberSumVec
import AFTD.Kb.Optimization.IsGibbsStochastic

/-!
# target_prefix_capacity_eq_population

Topic: submodular   Node: b1c42cd45308

Provenance: helper lemma. arXiv:2610.35433, Eq. (6)

For any natural number n, population vector y in stdSimplex ℝ (Fin n), Gibbs vector γ in stdSimplex ℝ (Fin n) with strictly positive entries (∀ i, 0 < γ i), permutation π of Fin n satisfying Antitone (fun i : Fin n => y (π i) / γ (π i)), and natural number k ≤ n, the population capacity population_capacity γ y (thermomajorization_prefix π k) equals the sum ∑ i ∈ thermomajorization_prefix π k, y i.
-/

private lemma target_prefix_capacity_eq_population_key {n : ℕ}
    {y γ : Fin n → ℝ} (hγ_pos : ∀ i, 0 < γ i) (π : Equiv.Perm (Fin n))
    (hπ : Antitone (fun i : Fin n => y (π i) / γ (π i))) (k : ℕ) (hk : k ≤ n)
    {c : Fin n → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hsum : ∑ j, c j * γ j = ∑ j ∈ thermomajorization_prefix π k, γ j) :
    ∑ j, c j * y j ≤ ∑ j ∈ thermomajorization_prefix π k, y j := by
  classical
  set S := thermomajorization_prefix π k with hSdef
  set d : Fin n → ℝ := fun j => c j - (if j ∈ S then (1:ℝ) else 0) with hddef
  have hmem : ∀ j : Fin n, j ∈ S ↔ ∃ i : Fin n, (i : ℕ) < k ∧ π i = j := by
    intro j; rw [hSdef]
    rw [thermomajorization_prefix, Finset.mem_map]
    simp only [Equiv.coe_toEmbedding, Finset.mem_filter, Finset.mem_univ, true_and]
  have hind : ∀ f : Fin n → ℝ, ∑ j, (if j ∈ S then (1:ℝ) else 0) * f j = ∑ j ∈ S, f j := by
    intro f
    have h1 : ∑ j, (if j ∈ S then (1:ℝ) else 0) * f j = ∑ j, (if j ∈ S then f j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with h <;> simp
    rw [h1, ← Finset.sum_filter]
    congr 1
    ext j
    simp
  have hdγ : ∑ j, d j * γ j = 0 := by
    have hsplit : ∑ j, d j * γ j = ∑ j, c j * γ j - ∑ j, (if j ∈ S then (1:ℝ) else 0) * γ j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hddef]
      simp only
      ring
    rw [hsplit, hind γ, hsum, sub_self]
  have hdy : ∑ j, d j * y j = ∑ j, c j * y j - ∑ j ∈ S, y j := by
    have hsplit : ∑ j, d j * y j = ∑ j, c j * y j - ∑ j, (if j ∈ S then (1:ℝ) else 0) * y j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hddef]
      simp only
      ring
    rw [hsplit, hind y]
  by_cases hk0 : k = 0
  · have hSe : S = ∅ := by
      rw [hSdef, hk0]
      ext j
      simp [thermomajorization_prefix]
    have hsum0 : ∑ j, c j * γ j = 0 := by rw [hsum, hSe]; simp
    have hcz : ∀ j, c j = 0 := by
      intro j
      have hle : c j * γ j ≤ ∑ i, c i * γ i :=
        Finset.single_le_sum (f := fun i => c i * γ i)
          (fun i _ => mul_nonneg (hc0 i) (le_of_lt (hγ_pos i))) (Finset.mem_univ j)
      have hnonneg : 0 ≤ c j * γ j := mul_nonneg (hc0 j) (le_of_lt (hγ_pos j))
      have hzero : c j * γ j = 0 := by linarith
      exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (hγ_pos j))
    simp [hcz, hSe]
  · have hk1 : 0 < k := Nat.pos_of_ne_zero hk0
    have hmk : k - 1 < n := by omega
    set m : Fin n := ⟨k - 1, hmk⟩ with hmdef
    have hmval : (m : ℕ) = k - 1 := rfl
    set rstar : ℝ := y (π m) / γ (π m) with hrstardef
    have hFj_ge : ∀ j : Fin n, j ∈ S → rstar ≤ y j / γ j := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := (hmem j).mp hj
      have hle : i ≤ m := by
        simp only [Fin.le_iff_val_le_val, hmval]; omega
      have hh := hπ hle
      simpa [hrstardef] using hh
    have hFj_le : ∀ j : Fin n, j ∉ S → y j / γ j ≤ rstar := by
      intro j hj
      have hge : ¬ ((π.symm j : Fin n) : ℕ) < k := by
        intro hlt
        exact hj ((hmem j).mpr ⟨π.symm j, hlt, by simp⟩)
      have hle : m ≤ π.symm j := by
        simp only [Fin.le_iff_val_le_val, hmval]; omega
      have hh := hπ hle
      simpa [hrstardef] using hh
    have hpoint : ∀ j, d j * y j ≤ d j * (rstar * γ j) := by
      intro j
      by_cases hj : j ∈ S
      · have hdle : d j ≤ 0 := by
          have : d j = c j - 1 := by rw [hddef]; simp [hj]
          rw [this]; linarith [hc1 j]
        have hγj := hγ_pos j
        have h1 : rstar * γ j ≤ (y j / γ j) * γ j :=
          mul_le_mul_of_nonneg_right (hFj_ge j hj) (le_of_lt hγj)
        have h2 : (y j / γ j) * γ j = y j := div_mul_cancel₀ _ (ne_of_gt hγj)
        have hnn : 0 ≤ y j - rstar * γ j := by linarith
        have h3 := mul_nonpos_of_nonpos_of_nonneg hdle hnn
        nlinarith [h3]
      · have hdge : 0 ≤ d j := by
          have : d j = c j := by rw [hddef]; simp [hj]
          rw [this]; exact hc0 j
        have hγj := hγ_pos j
        have h1 : (y j / γ j) * γ j ≤ rstar * γ j :=
          mul_le_mul_of_nonneg_right (hFj_le j hj) (le_of_lt hγj)
        have h2 : (y j / γ j) * γ j = y j := div_mul_cancel₀ _ (ne_of_gt hγj)
        have hnn : y j - rstar * γ j ≤ 0 := by linarith
        have h3 := mul_nonpos_of_nonneg_of_nonpos hdge hnn
        nlinarith [h3]
    have hbound : ∑ j, d j * y j ≤ 0 := by
      calc ∑ j, d j * y j ≤ ∑ j, d j * (rstar * γ j) := Finset.sum_le_sum (fun j _ => hpoint j)
        _ = rstar * ∑ j, d j * γ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = 0 := by rw [hdγ]; ring
    linarith

/-- The target state saturates its own population capacity on all thermomajorization prefix sets. -/
theorem target_prefix_capacity_eq_population {n : ℕ}
    {y γ : Fin n → ℝ} (hy : y ∈ stdSimplex ℝ (Fin n)) (hγ : γ ∈ stdSimplex ℝ (Fin n))
    (hγ_pos : ∀ i, 0 < γ i) (π : Equiv.Perm (Fin n))
    (hπ : Antitone (fun i : Fin n => y (π i) / γ (π i))) (k : ℕ) (hk : k ≤ n) :
    population_capacity γ y (thermomajorization_prefix π k) =
      ∑ i ∈ thermomajorization_prefix π k, y i := by
  classical
  have _ := hγ
  set S := thermomajorization_prefix π k with hSdef
  have hself : y ∈ thermally_reachable_block_populations (id : Fin n → Fin n) γ y := by
    refine ⟨y, hy, ?_, ?_⟩
    · exact ⟨fun i j => if i = j then (1:ℝ) else 0, by
        refine ⟨?_, ?_, ?_⟩
        · intro i j; dsimp only; split_ifs <;> norm_num
        · intro j; rw [Finset.sum_ite_eq']; simp
        · intro i
          have h1 : ∑ j, (if i = j then (1:ℝ) else 0) * γ j = ∑ j, (if i = j then γ j else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          rw [h1, Finset.sum_ite_eq]; simp, by
        intro i
        have h1 : ∑ j, (if i = j then (1:ℝ) else 0) * y j = ∑ j, (if i = j then y j else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp
        rw [h1, Finset.sum_ite_eq]; simp⟩
    · funext j
      unfold fiber_sum_vec
      rw [Finset.sum_filter]
      simp only [id]
      rw [Finset.sum_ite_eq']
      simp
  set A := (fun p : Fin n → ℝ => ∑ i ∈ S, p i) '' thermally_reachable_block_populations (id : Fin n → Fin n) γ y with hAdef
  have hmem : ∑ i ∈ S, y i ∈ A := ⟨y, hself, rfl⟩
  have hupper : ∀ a ∈ A, a ≤ ∑ i ∈ S, y i := by
    rintro a ⟨p, hp, rfl⟩
    obtain ⟨x', hx', htr, hp_eq⟩ := hp
    subst hp_eq
    obtain ⟨T, hT, hTx⟩ := htr
    have hfib : ∀ i : Fin n, fiber_sum_vec (id : Fin n → Fin n) x' i = x' i := by
      intro i
      unfold fiber_sum_vec
      rw [Finset.sum_filter]
      simp only [id]
      rw [Finset.sum_ite_eq']
      simp
    simp only [hfib]
    have hrewrite : ∑ i ∈ S, x' i = ∑ j, (∑ i ∈ S, T i j) * y j := by
      have step1 : ∑ i ∈ S, x' i = ∑ i ∈ S, ∑ j, T i j * y j := by
        apply Finset.sum_congr rfl
        intro i _
        exact hTx i
      have step2 : ∑ i ∈ S, ∑ j, T i j * y j = ∑ j, ∑ i ∈ S, T i j * y j := Finset.sum_comm
      have step3 : ∑ j, ∑ i ∈ S, T i j * y j = ∑ j, (∑ i ∈ S, T i j) * y j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      rw [step1, step2, step3]
    rw [hrewrite]
    have hc0 : ∀ j, 0 ≤ ∑ i ∈ S, T i j := fun j => Finset.sum_nonneg (fun i _ => hT.1 i j)
    have hc1 : ∀ j, ∑ i ∈ S, T i j ≤ 1 := by
      intro j
      have hle : ∑ i ∈ S, T i j ≤ ∑ i, T i j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hT.1 i j)
      rw [hT.2.1 j] at hle
      exact hle
    have hsumc : ∑ j, (∑ i ∈ S, T i j) * γ j = ∑ j ∈ S, γ j := by
      have step1 : ∑ j, (∑ i ∈ S, T i j) * γ j = ∑ j, ∑ i ∈ S, T i j * γ j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      have step2 : ∑ j, ∑ i ∈ S, T i j * γ j = ∑ i ∈ S, ∑ j, T i j * γ j := Finset.sum_comm
      have step3 : ∑ i ∈ S, ∑ j, T i j * γ j = ∑ i ∈ S, γ i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hT.2.2 i
      rw [step1, step2, step3]
    exact target_prefix_capacity_eq_population_key hγ_pos π hπ k hk hc0 hc1 hsumc
  have hbdd : BddAbove A := ⟨_, hupper⟩
  have h1 : ∑ i ∈ S, y i ≤ sSup A := le_csSup hbdd hmem
  have h2 : sSup A ≤ ∑ i ∈ S, y i := csSup_le ⟨_, hmem⟩ hupper
  rw [population_capacity, block_population_capacity, ← hAdef]
  exact le_antisymm h2 h1
