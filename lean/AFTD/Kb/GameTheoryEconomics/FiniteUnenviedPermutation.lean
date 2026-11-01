import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteEnvyCycleImprovement

/-!
# finite_unenvied_permutation

Topic: fair_division   Node: c823221164e3

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

Every finite nonempty matrix of real bundle values admits a permutation that weakly improves each diagonal value and has an unenvied column in the permuted assignment.
-/

open Function Finset

theorem finite_unenvied_permutation {α : Type*} [Fintype α] [Nonempty α]
    (w : α → α → ℝ) :
    ∃ p : Equiv.Perm α, (∀ i, w i i ≤ w i (p i)) ∧
      ∃ s, ∀ i, w i (p s) ≤ w i (p i) := by
  classical
  let S : Finset (Equiv.Perm α) := Finset.univ.filter (fun p => ∀ i, w i i ≤ w i (p i))
  have hS : S.Nonempty := ⟨Equiv.refl α, by simp [S]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun p => ∑ i, w i (p i)) hS
  refine ⟨p, (Finset.mem_filter.mp hp).2, ?_⟩
  by_contra hn
  push Not at hn
  obtain ⟨q, hq, j, hj⟩ := finite_envy_cycle_improvement (fun i k => w i (p k)) hn
  have hnew : q.trans p ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    exact ((Finset.mem_filter.mp hp).2 i).trans (hq i)
  have hlt : (∑ i, w i (p i)) < ∑ i, w i ((q.trans p) i) := by
    exact Finset.sum_lt_sum (fun i _ => hq i) ⟨j, Finset.mem_univ _, hj⟩
  exact (not_lt_of_ge (hmax (q.trans p) hnew)) hlt
