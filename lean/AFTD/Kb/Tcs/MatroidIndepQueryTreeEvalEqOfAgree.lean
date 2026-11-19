import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIndepQueryTree
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval

/-!
# matroid_indep_query_tree_eval_eq_of_agree

Topic: algorithms   Node: c463bf66152b

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

On an oracle o, an independence-query tree T asks at most depth(T) sets: there is a family L of at most depth(T) finite sets such that every oracle agreeing with o on L gives the same output.
-/

theorem matroid_indep_query_tree_eval_eq_of_agree {α : Type*} (o : Finset α → Bool) (T : MatroidIndepQueryTree α) :
    ∃ L : Finset (Finset α), L.card ≤ T.depth ∧
      ∀ o' : Finset α → Bool, (∀ S ∈ L, o' S = o S) → T.eval o' = T.eval o := by
  classical
  induction T with
  | leaf b => exact ⟨∅, by simp [MatroidIndepQueryTree.depth], fun o' _ => rfl⟩
  | query S no yes ihn ihy =>
    obtain ⟨Ln, hLn, hn⟩ := ihn
    obtain ⟨Ly, hLy, hy⟩ := ihy
    by_cases hc : o S = true
    · refine ⟨insert S Ly, ?_, fun o' h => ?_⟩
      · have := Finset.card_insert_le S Ly
        simp only [MatroidIndepQueryTree.depth]
        omega
      · have hS : o' S = o S := h S (Finset.mem_insert_self S Ly)
        simp only [MatroidIndepQueryTree.eval, hS, hc, if_true]
        exact hy o' fun S' hS' => h S' (Finset.mem_insert_of_mem hS')
    · refine ⟨insert S Ln, ?_, fun o' h => ?_⟩
      · have := Finset.card_insert_le S Ln
        simp only [MatroidIndepQueryTree.depth]
        omega
      · have hS : o' S = o S := h S (Finset.mem_insert_self S Ln)
        simp only [MatroidIndepQueryTree.eval, hS, hc]
        exact hn o' fun S' hS' => h S' (Finset.mem_insert_of_mem hS')
