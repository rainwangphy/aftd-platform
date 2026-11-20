import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTef1
import AFTD.Kb.GameTheoryEconomics.ChorePrefixBundle
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# tef1_exists_le_three_chores_three_agents

Topic: fair_division   Node: 8a5605325551

Provenance: helper lemma. arXiv:2611.25892 Sec. 7

For every natural number m ≤ 3 and every cost matrix d : Fin 3 → Fin m → ℝ with nonnegative entries (∀ i c, 0 ≤ d i c), there exists an allocation π : Fin m → Fin 3 that is temporal EF1 (is_tef1 3 m d π).
-/

/-- A TEF1 allocation always exists for three agents and at most three chores. -/
theorem tef1_exists_le_three_chores_three_agents (m : ℕ) (hm : m ≤ 3)
    (d : Fin 3 → Fin m → ℝ) (hd : ∀ i c, 0 ≤ d i c) :
    ∃ π : Fin m → Fin 3, is_tef1 3 m d π := by
  let π : Fin m → Fin 3 := fun c => ⟨c.val, lt_of_lt_of_le c.isLt hm⟩
  refine ⟨π, ?_⟩
  have hπinj : Function.Injective π := by
    intro a b hab
    have h : a.val = b.val := by
      have := congrArg (fun x : Fin 3 => x.val) hab
      simpa [π] using this
    exact Fin.ext h
  have hnonneg : ∀ (u : Fin m → ℝ) (S : Finset (Fin m)), (∀ c, 0 ≤ u c) →
      0 ≤ additive_valuation u S := by
    intro u S hu
    simp only [additive_valuation]
    exact Finset.sum_nonneg (fun c _ => hu c)
  intro t i j hij
  by_cases hne : (chore_prefix_bundle π t i).Nonempty
  · obtain ⟨c, hc⟩ := hne
    right
    refine ⟨c, hc, ?_⟩
    have hsingle : chore_prefix_bundle π t i = {c} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      refine ⟨hc, ?_⟩
      intro b hb
      simp only [chore_prefix_bundle, Finset.mem_filter, Finset.mem_univ, true_and] at hb hc
      exact hπinj (hb.2.trans hc.2.symm)
    have h2 := hnonneg (d i) (chore_prefix_bundle π t j) (fun c => hd i c)
    rw [hsingle, additive_valuation, Finset.sum_singleton]
    linarith
  · left
    have hempty : chore_prefix_bundle π t i = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    have h2 := hnonneg (d i) (chore_prefix_bundle π t j) (fun c => hd i c)
    rw [hempty, additive_valuation, Finset.sum_empty]
    linarith
