import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AnyPriceShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IsProp1Fair

/-!
# aps_fair_not_imp_prop1_fair

Topic: fair_division   Node: e84058b5db37

Open problem 2 of arXiv:2502.02815 has a negative answer: for additive goods with unequal entitlements, an allocation can give every agent her AnyPrice share and still fail PROP1, already with two agents. Example: three goods worth (2, 1, 1) to both agents, entitlements 4/5 and 1/5; the first agent gets the good worth 2.
-/

theorem aps_fair_not_imp_prop1_fair :
    ¬ ∀ (m : ℕ) (u : Fin 2 → Fin m → ℝ) (w : Fin 2 → ℝ),
      (∀ i j, 0 ≤ u i j) → (∀ i, 0 < w i) → ∑ i, w i = 1 →
      ∀ σ : Fin m → Fin 2,
        (∀ i, any_price_share (additive_valuation (u i)) (w i) ≤
          additive_valuation (u i) (bundle_of σ i)) →
        ∀ i, is_prop1_fair (additive_valuation (u i)) (w i) (bundle_of σ i) := by
  intro h
  -- two agents, three goods worth (2, 1, 1) to both; entitlements 4/5 and 1/5;
  -- agent 0 gets the big good, agent 1 the two small ones
  set u : Fin 2 → Fin 3 → ℝ := fun _ => ![2, 1, 1] with hu
  set w : Fin 2 → ℝ := ![4 / 5, 1 / 5] with hw
  set σ : Fin 3 → Fin 2 := ![0, 1, 1] with hσ
  have hval : ∀ i (S : Finset (Fin 3)), 0 ≤ additive_valuation (u i) S := by
    intro i S
    apply Finset.sum_nonneg
    intro j _
    fin_cases j <;> simp [hu]
  -- the price-indexed value is bounded below by 0, so the AnyPrice share is an honest infimum
  have hbdd : ∀ i, BddBelow (Set.range fun p : Fin 3 → ℝ =>
      ⨆ S : {S : Finset (Fin 3) // ∑ j ∈ S, p j ≤ w i * ∑ j, p j},
        additive_valuation (u i) (S : Finset (Fin 3))) := by
    intro i
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hwi : 0 ≤ w i ∧ w i ≤ 1 := by fin_cases i <;> simp [hw] <;> norm_num
    by_cases hp : 0 ≤ ∑ j, p j
    · have hS : ∑ j ∈ (∅ : Finset (Fin 3)), p j ≤ w i * ∑ j, p j := by
        simp only [Finset.sum_empty]; exact mul_nonneg hwi.1 hp
      exact le_trans (hval i ∅) (le_ciSup (f := fun S : {S : Finset (Fin 3) // ∑ j ∈ S, p j ≤ w i * ∑ j, p j} => additive_valuation (u i) (S : Finset (Fin 3))) (Set.finite_range _).bddAbove ⟨∅, hS⟩)
    · have hS : ∑ j ∈ (Finset.univ : Finset (Fin 3)), p j ≤ w i * ∑ j, p j := by
        rw [not_le] at hp; nlinarith [hwi.2]
      exact le_trans (hval i Finset.univ) (le_ciSup (f := fun S : {S : Finset (Fin 3) // ∑ j ∈ S, p j ≤ w i * ∑ j, p j} => additive_valuation (u i) (S : Finset (Fin 3))) (Set.finite_range _).bddAbove ⟨_, hS⟩)
  -- a price vector at which every affordable bundle is worth at most `b`
  have hwit : ∀ i (p : Fin 3 → ℝ) (b : ℝ), 0 ≤ ∑ j, p j →
      (∀ S : Finset (Fin 3), ∑ j ∈ S, p j ≤ w i * ∑ j, p j → additive_valuation (u i) S ≤ b) →
      any_price_share (additive_valuation (u i)) (w i) ≤ b := by
    intro i p b hp hS
    have hwi : 0 ≤ w i := by fin_cases i <;> simp [hw] <;> norm_num
    have : Nonempty {S : Finset (Fin 3) // ∑ j ∈ S, p j ≤ w i * ∑ j, p j} :=
      ⟨⟨∅, by simp only [Finset.sum_empty]; exact mul_nonneg hwi hp⟩⟩
    exact le_trans (ciInf_le (hbdd i) p) (ciSup_le fun S => hS S.1 S.2)
  have hb0 : bundle_of σ 0 = {0} := by decide
  have hb1 : bundle_of σ 1 = {1, 2} := by decide
  have hfair := h 3 u w (fun i j => by fin_cases i <;> fin_cases j <;> simp [hu])
    (fun i => by fin_cases i <;> simp [hw]) (by simp [hw, Fin.sum_univ_two]; norm_num) σ
    (by
      intro i
      fin_cases i
      · -- agent 0: at prices (81/100, 19/200, 19/200) the big good is out of reach
        refine hwit 0 ![81 / 100, 19 / 200, 19 / 200] _ (by simp [Fin.sum_univ_three]; norm_num) ?_
        intro S hS
        have hsplit : ∀ S : Finset (Fin 3), 0 ∈ S ∨ S ⊆ {1, 2} := by decide
        rcases hsplit S with h0 | hsub
        · exfalso
          have : (81 / 100 : ℝ) ≤ ∑ j ∈ S, (![81 / 100, 19 / 200, 19 / 200] : Fin 3 → ℝ) j := by
            have := Finset.single_le_sum (f := (![81 / 100, 19 / 200, 19 / 200] : Fin 3 → ℝ))
              (fun j _ => by fin_cases j <;> simp <;> norm_num) h0
            simpa using this
          simp [hw, Fin.sum_univ_three] at hS
          norm_num at hS
          linarith
        · show additive_valuation (u 0) S ≤ additive_valuation (u 0) (bundle_of σ 0)
          rw [hb0]
          calc additive_valuation (u 0) S ≤ additive_valuation (u 0) {1, 2} :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun j _ _ => by fin_cases j <;> simp [hu])
            _ = additive_valuation (u 0) {0} := by simp [additive_valuation, hu]; norm_num
      · -- agent 1: at equal prices no good fits a budget of 1/5
        refine hwit 1 ![1 / 3, 1 / 3, 1 / 3] _ (by simp [Fin.sum_univ_three]; norm_num) ?_
        intro S hS
        have hsplit : ∀ S : Finset (Fin 3), S = ∅ ∨ ∃ j, j ∈ S := by
          intro S
          rcases S.eq_empty_or_nonempty with h | h
          · exact Or.inl h
          · exact Or.inr h
        rcases hsplit S with rfl | ⟨j, hj⟩
        · simpa [additive_valuation] using hval 1 (bundle_of σ 1)
        · exfalso
          have : (1 / 3 : ℝ) ≤ ∑ j ∈ S, (![1 / 3, 1 / 3, 1 / 3] : Fin 3 → ℝ) j := by
            have := Finset.single_le_sum (f := (![1 / 3, 1 / 3, 1 / 3] : Fin 3 → ℝ))
              (fun j _ => by fin_cases j <;> simp) hj
            fin_cases j <;> simpa using this
          simp [hw, Fin.sum_univ_three] at hS
          norm_num at hS
          linarith)
  -- agent 0 is not PROP1-satisfied: 2 < 16/5, and 2 + 1 = 3 < 16/5
  have hp := hfair 0
  rw [hb0] at hp
  simp only [is_prop1_fair, additive_valuation, hu, hw] at hp
  simp [Fin.sum_univ_three] at hp
  norm_num at hp
  rcases hp with ⟨g, hg, hlt⟩
  fin_cases g <;> simp at hg hlt <;> norm_num at hlt
