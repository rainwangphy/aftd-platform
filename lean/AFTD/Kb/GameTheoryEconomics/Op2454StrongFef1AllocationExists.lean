import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsStrongFef1Agents
import AFTD.Kb.GameTheoryEconomics.IsFef1Charity
import AFTD.Kb.GameTheoryEconomics.IsBudgetFeasible
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.Charity

/-!
# op_2454_strong_fef1_allocation_exists

Topic: fair_division   Node: b9056d163fae

Provenance: formalization of a published result. Source: arXiv:2611.34488 Sec. 6

Open Problem OP-2454 (arXiv:2611.34488, Sec. 6): For any number of agents n and goods m, strictly positive item sizes s : Fin m → ℝ (∀ g, 0 < s g), nonnegative individual budgets B : Fin n → ℝ (∀ i, 0 ≤ B i), and nonnegative item values v : Fin n → Fin m → ℝ (∀ i g, 0 ≤ v i g), there exists an allocation A : Fin n → Finset (Fin m) that is budget-feasible (is_budget_feasible s B A), satisfies strong FEF1 between agents (is_strong_fef1_agents s B v A), and satisfies FEF1 towards the charity (is_fef1_charity s B v A).
-/

/-- Open Problem OP-2454: existence of an allocation satisfying strong FEF1 between agents and FEF1 towards charity under heterogeneous budget constraints. -/
theorem op_2454_strong_fef1_allocation_exists (n m : ℕ)
    (s : Fin m → ℝ) (hs : ∀ g, 0 < s g)
    (B : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i)
    (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : Fin n → Finset (Fin m),
      is_budget_feasible s B A ∧
      is_strong_fef1_agents s B v A ∧
      is_fef1_charity s B v A := by
  classical
  have hmono : ∀ i (S T : Finset (Fin m)), S ⊆ T →
      additive_valuation (v i) S ≤ additive_valuation (v i) T := by
    intro i S T hST
    exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun g _ _ => hv i g)
  -- P: budget feasible and envy-free up to any good (towards proper subsets) between agents
  let P : (Fin n → Finset (Fin m)) → Prop := fun A => is_budget_feasible s B A ∧
    ∀ i j, i ≠ j → ∀ T, T ⊆ A j → T ≠ A j → additive_valuation s T ≤ B i →
      additive_valuation (v i) T ≤ additive_valuation (v i) (A i)
  let W : (Fin n → Finset (Fin m)) → ℝ := fun A => ∑ i, additive_valuation (v i) (A i)
  have hP0 : P (fun _ => ∅) := by
    refine ⟨⟨fun i j _ => by simp, fun i => by simp [additive_valuation, hB i]⟩, ?_⟩
    intro i j _ T hT hne
    exact absurd (Finset.subset_empty.mp hT) hne
  obtain ⟨A, hAmem, hAmax⟩ := Finset.exists_max_image (Finset.univ.filter P) W
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP0⟩⟩
  have hA : P A := (Finset.mem_filter.mp hAmem).2
  have hmemC : ∀ g j, g ∈ charity A → g ∉ A j := by
    intro g j hg hgj
    simp only [charity, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and] at hg
    exact hg ⟨j, hgj⟩
  -- nobody envies an affordable subset of the charity
  have hEF : ∀ i T, T ⊆ charity A → additive_valuation s T ≤ B i →
      additive_valuation (v i) T ≤ additive_valuation (v i) (A i) := by
    by_contra hcon
    push Not at hcon
    let F := (Finset.univ : Finset (Finset (Fin m))).filter (fun T => T ⊆ charity A ∧
      ∃ k, additive_valuation s T ≤ B k ∧ additive_valuation (v k) (A k) < additive_valuation (v k) T)
    obtain ⟨i0, T0, hT0, hs0, hv0⟩ := hcon
    obtain ⟨S, hSmem, hSmin⟩ := Finset.exists_min_image F Finset.card
      ⟨T0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT0, i0, hs0, hv0⟩⟩
    obtain ⟨hSC, k, hSk, hvk⟩ := (Finset.mem_filter.mp hSmem).2
    let A' := Function.update A k S
    have hA'k : A' k = S := by simp [A']
    have hA'j : ∀ j, j ≠ k → A' j = A j := fun j hj => by simp [A', hj]
    have hP' : P A' := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i j hij
        by_cases hi : i = k
        · subst hi
          rw [hA'k, hA'j j (Ne.symm hij)]
          exact Finset.disjoint_left.mpr fun g hg => hmemC g j (hSC hg)
        · by_cases hj : j = k
          · subst hj
            rw [hA'k, hA'j i hi]
            exact Finset.disjoint_right.mpr fun g hg => hmemC g i (hSC hg)
          · rw [hA'j i hi, hA'j j hj]; exact hA.1.1 hij
      · intro i
        by_cases hi : i = k
        · subst hi; rw [hA'k]; exact hSk
        · rw [hA'j i hi]; exact hA.1.2 i
      · intro i j hij T hT hne hsT
        by_cases hj : j = k
        · subst hj
          have hi : i ≠ j := hij
          rw [hA'k] at hT hne
          rw [hA'j i hi]
          by_contra hlt
          push Not at hlt
          have hTF : T ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT.trans hSC, i, hsT, hlt⟩
          have := hSmin T hTF
          have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hT, hne⟩)
          omega
        · rw [hA'j j hj] at hT hne
          by_cases hi : i = k
          · subst hi
            rw [hA'k]
            exact (hA.2 i j hij T hT hne hsT).trans hvk.le
          · rw [hA'j i hi]; exact hA.2 i j hij T hT hne hsT
    have hW : W A < W A' := by
      apply Finset.sum_lt_sum
      · intro i _
        by_cases hi : i = k
        · subst hi; rw [hA'k]; exact hvk.le
        · rw [hA'j i hi]
      · exact ⟨k, Finset.mem_univ _, by rw [hA'k]; exact hvk⟩
    have := hAmax A' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)
    linarith
  refine ⟨A, hA.1, ?_, ?_⟩
  · intro i j hij hne
    obtain ⟨g, hg⟩ := hne
    refine ⟨g, hg, fun T hT hsT => hA.2 i j hij T (hT.trans (Finset.erase_subset _ _)) ?_ hsT⟩
    intro hTe
    have : g ∈ T := hTe ▸ hg
    exact (Finset.notMem_erase g (A j)) (hT this)
  · intro i T hT hne hsT
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, hg, (hmono i _ _ (Finset.erase_subset g T)).trans (hEF i T hT hsT)⟩
