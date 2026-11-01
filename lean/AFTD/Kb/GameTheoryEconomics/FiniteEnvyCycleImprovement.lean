import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteFunctionExistsPositivePeriod

/-!
# finite_envy_cycle_improvement

Topic: fair_division   Node: eb36dfd8f8a4

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

For a finite nonempty matrix of real bundle values, if every bundle is strictly envied by an agent relative to her own bundle, some bundle permutation weakly improves every diagonal value and strictly improves at least one.
-/

open Function Finset

theorem finite_envy_cycle_improvement {α : Type*} [Fintype α] [Nonempty α]
    (w : α → α → ℝ) (h : ∀ j, ∃ i, w i i < w i j) :
    ∃ p : Equiv.Perm α, (∀ i, w i i ≤ w i (p i)) ∧ ∃ i, w i i < w i (p i) := by
  classical
  choose f hf using h
  obtain ⟨k, hk, x, hx⟩ := finite_function_exists_positive_period f
  let C := Function.ptsOfPeriod f k
  let e : Equiv.Perm C := Equiv.ofBijective
    ((Function.bijOn_ptsOfPeriod f hk).mapsTo.restrict f C C)
    (Function.bijOn_ptsOfPeriod f hk).bijective
  let q : Equiv.Perm α := Equiv.Perm.ofSubtype e
  have hq (j : α) (hj : j ∈ C) : q j = f j := by
    exact Equiv.Perm.ofSubtype_apply_of_mem e hj
  have hfix (j : α) (hj : j ∉ C) : q j = j := by
    exact Equiv.Perm.ofSubtype_apply_of_not_mem e hj
  refine ⟨q.symm, ?_, ?_⟩
  · intro i
    by_cases hi : q.symm i ∈ C
    · have hh := hf (q.symm i)
      rw [← hq (q.symm i) hi, q.apply_symm_apply] at hh
      exact hh.le
    · have hh := hfix (q.symm i) hi
      rw [q.apply_symm_apply] at hh
      rw [← hh]
  · refine ⟨q x, ?_⟩
    rw [q.symm_apply_apply, hq x hx]
    exact hf x
