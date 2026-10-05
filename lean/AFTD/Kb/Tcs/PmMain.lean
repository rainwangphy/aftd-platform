import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetWidth2
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PMPosetMinSet
import AFTD.Kb.Tcs.PMTree
import AFTD.Kb.Tcs.PMTreeRun
import AFTD.Kb.Tcs.PMTreeCost
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PMSat
import AFTD.Kb.Tcs.PmFamWidth2
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot
import AFTD.Kb.Tcs.PMStateStep
import AFTD.Kb.Tcs.PmStepFacts
import AFTD.Kb.Tcs.PmStepInv
import AFTD.Kb.Tcs.PmLeaf

/-!
# pm_main

Topic: algorithms   Node: 9d80e38054fc

Main adversary lemma: against any decision tree that is correct on all width-2 posets consistent with the answers so far, the adversary forces at least pot further queries.
-/

/-- Main adversary lemma: against any decision tree that is correct on all width-2 posets consistent with the answers so far, the adversary forces at least `pot` further queries. -/
theorem pm_main {n : ℕ} (T : PMTree n) : ∀ S : PMState n, S.Inv →
    (∀ P : PMPoset n, P.Width2 → PMSat P S.facts → T.run P = P.minSet) →
    ∃ P : PMPoset n, P.Width2 ∧ PMSat P S.facts ∧ S.pot ≤ (T.cost P : ℤ) := by
  induction T with
  | leaf s =>
    intro S hI hC
    by_cases hp : S.pot ≤ 0
    · refine ⟨pmFam S.col S.rk, pm_fam_width2 _ _ hI.2.2.2.2.2.1, hI.2.1, ?_⟩
      simp only [PMTree.cost, Nat.cast_zero]; exact hp
    · obtain ⟨P₁, P₂, hw1, hw2, hs1, hs2, hne⟩ := pm_leaf S hI (by linarith)
      have e1 := hC P₁ hw1 hs1
      have e2 := hC P₂ hw2 hs2
      simp only [PMTree.run] at e1 e2
      exact absurd (e1.symm.trans e2) hne
  | node a b k ih =>
    intro S hI hC
    obtain ⟨hI', hpot⟩ := pm_step_inv S a b hI
    have hF : (S.step a b).2.facts = (a, b, (S.step a b).1) :: S.facts := pm_step_facts S a b
    have hans : ∀ P : PMPoset n, PMSat P (S.step a b).2.facts → P.ans a b = (S.step a b).1 := by
      intro P hP
      have := hP _ (by rw [hF]; exact List.mem_cons.2 (Or.inl rfl))
      simpa using this
    have hold : ∀ P : PMPoset n, PMSat P (S.step a b).2.facts → PMSat P S.facts := by
      intro P hP f hf
      exact hP f (by rw [hF]; exact List.mem_cons.2 (Or.inr hf))
    have hC' : ∀ P : PMPoset n, P.Width2 → PMSat P (S.step a b).2.facts →
        (k (S.step a b).1).run P = P.minSet := by
      intro P hP hS
      have := hC P hP (hold P hS)
      simp only [PMTree.run, hans P hS] at this
      exact this
    obtain ⟨P, hP, hS, hcost⟩ := ih (S.step a b).1 (S.step a b).2 hI' hC'
    refine ⟨P, hP, hold P hS, ?_⟩
    simp only [PMTree.cost, hans P hS]
    push_cast
    linarith
