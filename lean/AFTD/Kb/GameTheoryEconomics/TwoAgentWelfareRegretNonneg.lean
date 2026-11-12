import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoAgentWelfareRegret
import AFTD.Kb.GameTheoryEconomics.TwoAgentDraftWelfare
import AFTD.Kb.GameTheoryEconomics.TwoAgentFirstBestWelfare
import AFTD.Kb.GameTheoryEconomics.DraftAlloc
import AFTD.Kb.GameTheoryEconomics.DraftRule
import AFTD.Kb.GameTheoryEconomics.BalancedDraftValueOrder

/-!
# two_agent_welfare_regret_nonneg

Topic: fair_division   Node: d3db8af6a36d

Provenance: helper lemma. arXiv:2611.09685

For any number of goods m : ℕ, any drafting schedule s : Fin m → Fin 2 of length m, and any nonnegative valuation profile v : Fin 2 → Fin m → ℝ, the utilitarian welfare regret two_agent_welfare_regret m s v is nonnegative.
-/

lemma two_agent_welfare_regret_nonneg_draft_alloc_subset
    {Agent Object : Type*} [DecidableEq Agent] [DecidableEq Object]
    (succ : Agent → LinearOrder Object) (l : List Agent) (rem : Finset Object) (i : Agent) :
    draft_alloc succ l rem i ⊆ rem := by
  induction l generalizing rem i with
  | nil =>
    intro x hx
    simp [draft_alloc] at hx
  | cons a rest ih =>
    intro x hx
    unfold draft_alloc at hx
    split_ifs at hx with h
    · dsimp only at hx
      rcases eq_or_ne i a with rfl | hne
      · simp only [Function.update_apply, ite_true, Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact @Finset.max'_mem Object (succ i) rem h
        · exact Finset.mem_of_mem_erase (ih (rem.erase (@Finset.max' Object (succ i) rem h)) i hx)
      · have hne' : (i = a) = False := by simp [hne]
        simp only [Function.update_apply, hne', ite_false] at hx
        exact Finset.mem_of_mem_erase (ih (rem.erase (@Finset.max' Object (succ a) rem h)) i hx)
    · simp at hx

lemma two_agent_welfare_regret_nonneg_draft_alloc_disjoint
    {Agent Object : Type*} [DecidableEq Agent] [DecidableEq Object]
    (succ : Agent → LinearOrder Object) (l : List Agent) (rem : Finset Object)
    {i j : Agent} (hij : i ≠ j) :
    Disjoint (draft_alloc succ l rem i) (draft_alloc succ l rem j) := by
  induction l generalizing rem i j with
  | nil =>
    unfold draft_alloc
    exact Finset.disjoint_empty_left _
  | cons a rest ih =>
    unfold draft_alloc
    split_ifs with h
    · dsimp only
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy hxy
      subst hxy
      by_cases hia : i = a
      · have hja : ¬ j = a := by intro h; subst h; exact hij hia
        have h1 : (i = a) = True := by simp [hia]
        have h2 : (j = a) = False := by simp [hja]
        simp only [Function.update_apply, h1, ite_true, Finset.mem_insert] at hx
        simp only [Function.update_apply, h2, ite_false] at hy
        have hy_rem := two_agent_welfare_regret_nonneg_draft_alloc_subset succ rest
          (rem.erase (@Finset.max' Object (succ a) rem h)) j hy
        have hy_ne_max : x ≠ @Finset.max' Object (succ a) rem h := by
          intro h_eq
          subst h_eq
          exact (Finset.mem_erase.mp hy_rem).1 rfl
        rcases hx with rfl | hx'
        · exact hy_ne_max rfl
        · have hx'' : x ∈ draft_alloc succ rest (rem.erase (@Finset.max' Object (succ a) rem h)) i := by
            cases hia; exact hx'
          have hd := ih (rem := rem.erase (@Finset.max' Object (succ a) rem h)) hij
          exact Finset.disjoint_iff_ne.mp hd x hx'' x hy rfl
      · by_cases hja : j = a
        · have h1 : (i = a) = False := by simp [hia]
          have h2 : (j = a) = True := by simp [hja]
          simp only [Function.update_apply, h1, ite_false] at hx
          simp only [Function.update_apply, h2, ite_true, Finset.mem_insert] at hy
          have hx_rem := two_agent_welfare_regret_nonneg_draft_alloc_subset succ rest
            (rem.erase (@Finset.max' Object (succ a) rem h)) i hx
          have hx_ne_max : x ≠ @Finset.max' Object (succ a) rem h := by
            intro h_eq
            subst h_eq
            exact (Finset.mem_erase.mp hx_rem).1 rfl
          rcases hy with rfl | hy'
          · exact hx_ne_max rfl
          · have hy'' : x ∈ draft_alloc succ rest (rem.erase (@Finset.max' Object (succ a) rem h)) j := by
              cases hja; exact hy'
            have hd := ih (rem := rem.erase (@Finset.max' Object (succ a) rem h)) hij
            exact Finset.disjoint_iff_ne.mp hd x hx x hy'' rfl
        · have h1 : (i = a) = False := by simp [hia]
          have h2 : (j = a) = False := by simp [hja]
          simp only [Function.update_apply, h1, ite_false] at hx
          simp only [Function.update_apply, h2, ite_false] at hy
          have hd := ih (rem := rem.erase (@Finset.max' Object (succ a) rem h)) hij
          exact Finset.disjoint_iff_ne.mp hd x hx x hy rfl
    · simp only
      exact Finset.disjoint_empty_left _

/-- Utilitarian welfare regret in two-agent sincere drafting is nonnegative for nonnegative valuations. -/
theorem two_agent_welfare_regret_nonneg (m : ℕ) (s : Fin m → Fin 2) (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) :
    0 ≤ two_agent_welfare_regret m s v := by
  rw [two_agent_welfare_regret, sub_nonneg]
  unfold two_agent_draft_welfare two_agent_first_best_welfare
  rw [Fin.sum_univ_two]
  let succ := fun j => balanced_draft_value_order (v j)
  have hd : Disjoint (draft_rule s succ 0) (draft_rule s succ 1) := by
    exact two_agent_welfare_regret_nonneg_draft_alloc_disjoint succ (List.ofFn s) Finset.univ (by decide)
  have h0 : (∑ g ∈ draft_rule s succ 0, v 0 g) ≤ ∑ g ∈ draft_rule s succ 0, max (v 0 g) (v 1 g) := by
    apply Finset.sum_le_sum
    intro g _
    exact le_max_left (v 0 g) (v 1 g)
  have h1 : (∑ g ∈ draft_rule s succ 1, v 1 g) ≤ ∑ g ∈ draft_rule s succ 1, max (v 0 g) (v 1 g) := by
    apply Finset.sum_le_sum
    intro g _
    exact le_max_right (v 0 g) (v 1 g)
  have h_union : (∑ g ∈ draft_rule s succ 0, max (v 0 g) (v 1 g)) +
      (∑ g ∈ draft_rule s succ 1, max (v 0 g) (v 1 g)) =
      ∑ g ∈ draft_rule s succ 0 ∪ draft_rule s succ 1, max (v 0 g) (v 1 g) := by
    rw [Finset.sum_union hd]
  have h_sub : (∑ g ∈ draft_rule s succ 0 ∪ draft_rule s succ 1, max (v 0 g) (v 1 g)) ≤
      ∑ g : Fin m, max (v 0 g) (v 1 g) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro g _ _
    exact le_trans (hv 0 g) (le_max_left (v 0 g) (v 1 g))
  linarith
