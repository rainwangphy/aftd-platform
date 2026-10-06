import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetWidth2
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PMTree
import AFTD.Kb.Tcs.PMTreeRun
import AFTD.Kb.Tcs.PmAnsLt
import AFTD.Kb.Tcs.PmAnsGt
import AFTD.Kb.Tcs.PmAnsInc
import AFTD.Kb.Tcs.PmMinPre
import AFTD.Kb.Tcs.PmAlg
import AFTD.Kb.Tcs.PmStepEq
import AFTD.Kb.Tcs.PmMemMinPre

/-!
# pm_alg_run

Topic: algorithms   Node: fb2b02376079

Provenance: formalization of a published result. Source: Sorting and Selection in Posets, SODA 2009 / SIAM J. Comput. 2011 (arXiv:0707.1532), Section 4, Theorem 11 (correctness of the candidate-set algorithm); special case width 2

Correctness of the candidate-list algorithm on width-2 posets.
-/

open Finset in
/-- Correctness of the candidate-list algorithm on width-2 posets. -/
theorem pm_alg_run {n : ℕ} (P : PMPoset n) (hP : P.Width2) : ∀ (m k : ℕ) (cs : List (Fin n)),
    k + m = n → cs.length ≤ 2 → cs.Nodup → cs.toFinset = pmMinPre P k →
    (pmAlg m k cs).run P = pmMinPre P n := by
  intro m
  induction m with
  | zero =>
    intro k cs hkm _ _ hcs
    simp only [Nat.add_zero] at hkm
    subst hkm
    simp only [pmAlg, PMTree.run]
    exact hcs
  | succ m ih =>
    intro k cs hkm hlen hnd hcs
    have hk : k < n := by omega
    set x : Fin n := ⟨k, hk⟩ with hx
    rcases cs with _ | ⟨t, _ | ⟨t2, _ | ⟨t3, rest⟩⟩⟩
    · simp only [pmAlg, dif_pos hk]
      refine ih (k + 1) [x] (by omega) (by simp) (by simp)
        (pm_step_eq P k hk [] [x] hcs (fun a => ?_))
      simp [hx]
    · have ht := pm_mem_minPre P k t (by rw [← hcs]; simp)
      have hxt : x ≠ t := fun e => by rw [← e, hx] at ht; simp at ht
      simp only [pmAlg, dif_pos hk, PMTree.run]
      cases hr : P.ans x t
      · obtain ⟨f1, f2⟩ := pm_ans_lt P x t hr
        refine ih (k + 1) [x] (by omega) (by simp) (by simp)
          (pm_step_eq P k hk [t] [x] hcs (fun a => ?_))
        clear ih hcs hP
        rw [← hx]
        by_cases e1 : a = x <;> by_cases e2 : a = t <;> simp_all
      · obtain ⟨f1, f2⟩ := pm_ans_gt P x t hr
        refine ih (k + 1) [t] (by omega) (by simp) (by simp)
          (pm_step_eq P k hk [t] [t] hcs (fun a => ?_))
        clear ih hcs hP
        rw [← hx]
        by_cases e1 : a = x <;> by_cases e2 : a = t <;> simp_all
      · obtain ⟨f1, f2⟩ := pm_ans_inc P x t hr
        refine ih (k + 1) [t, x] (by omega) (by simp) (by simp [Ne.symm hxt])
          (pm_step_eq P k hk [t] [t, x] hcs (fun a => ?_))
        clear ih hcs hP
        rw [← hx]
        by_cases e1 : a = x <;> by_cases e2 : a = t <;> simp_all
    · have ht := pm_mem_minPre P k t (by rw [← hcs]; simp)
      have ht2 := pm_mem_minPre P k t2 (by rw [← hcs]; simp)
      have hxt : x ≠ t := fun e => by rw [← e, hx] at ht; simp at ht
      have hxt2 : x ≠ t2 := fun e => by rw [← e, hx] at ht2; simp at ht2
      have h12 : t ≠ t2 := by simpa using hnd
      have l12 : P.lt t t2 = false := ht2.2 t ht.1
      have l21 : P.lt t2 t = false := ht.2 t2 ht2.1
      simp only [pmAlg, dif_pos hk, PMTree.run]
      cases hr : P.ans x t
      · -- x ≺ t
        obtain ⟨f1, f2⟩ := pm_ans_lt P x t hr
        simp only [PMTree.run]
        cases hr2 : P.ans x t2
        · obtain ⟨g1, g2⟩ := pm_ans_lt P x t2 hr2
          refine ih (k + 1) [x] (by omega) (by simp) (by simp)
            (pm_step_eq P k hk [t, t2] [x] hcs (fun a => ?_))
          clear ih hcs hP
          rw [← hx]
          by_cases e1 : a = x <;> by_cases e2 : a = t <;> by_cases e3 : a = t2 <;> simp_all
        · obtain ⟨g1, g2⟩ := pm_ans_gt P x t2 hr2
          have := P.trans _ _ _ g2 f1
          rw [l21] at this
          exact absurd this (by simp)
        · obtain ⟨g1, g2⟩ := pm_ans_inc P x t2 hr2
          refine ih (k + 1) [t2, x] (by omega) (by simp) (by simp [Ne.symm hxt2])
            (pm_step_eq P k hk [t, t2] [t2, x] hcs (fun a => ?_))
          clear ih hcs hP
          rw [← hx]
          by_cases e1 : a = x <;> by_cases e2 : a = t <;> by_cases e3 : a = t2 <;> simp_all
      · -- t ≺ x
        obtain ⟨f1, f2⟩ := pm_ans_gt P x t hr
        have g1 : P.lt x t2 = false := by
          cases h : P.lt x t2
          · rfl
          · have := P.trans _ _ _ f2 h
            rw [l12] at this
            exact absurd this (by simp)
        refine ih (k + 1) [t, t2] (by omega) (by simp) (by simp [h12])
          (pm_step_eq P k hk [t, t2] [t, t2] hcs (fun a => ?_))
        clear ih hcs hP
        rw [← hx]
        by_cases e1 : a = x <;> by_cases e2 : a = t <;> by_cases e3 : a = t2 <;> simp_all
      · -- x ∥ t
        obtain ⟨f1, f2⟩ := pm_ans_inc P x t hr
        simp only [PMTree.run]
        cases hr2 : P.ans x t2
        · obtain ⟨g1, g2⟩ := pm_ans_lt P x t2 hr2
          refine ih (k + 1) [t, x] (by omega) (by simp) (by simp [Ne.symm hxt])
            (pm_step_eq P k hk [t, t2] [t, x] hcs (fun a => ?_))
          clear ih hcs hP
          rw [← hx]
          by_cases e1 : a = x <;> by_cases e2 : a = t <;> by_cases e3 : a = t2 <;> simp_all
        · obtain ⟨g1, g2⟩ := pm_ans_gt P x t2 hr2
          refine ih (k + 1) [t, t2] (by omega) (by simp) (by simp [h12])
            (pm_step_eq P k hk [t, t2] [t, t2] hcs (fun a => ?_))
          clear ih hcs hP
          rw [← hx]
          by_cases e1 : a = x <;> by_cases e2 : a = t <;> by_cases e3 : a = t2 <;> simp_all
        · obtain ⟨g1, g2⟩ := pm_ans_inc P x t2 hr2
          exfalso
          rcases hP x t t2 hxt h12 hxt2 with h | h | h | h | h | h <;> simp_all
    · simp at hlen
