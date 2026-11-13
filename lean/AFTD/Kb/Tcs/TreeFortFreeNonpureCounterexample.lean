import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZfsComplIffNoStuck
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# tree_fort_free_nonpure_counterexample

Topic: graphs   Node: 6661bb5cb2b8

Provenance: helper lemma. A four-vertex obstruction to a normalized-matching proof strategy for OP-1399.

A four-vertex tree has a maximal fort-free two-set and also a fort-free three-set.
-/

def tree_fort_free_nonpure_counterexample_edges : List (Fin 4 × Fin 4) :=
  [(1, 0), (1, 2), (0, 3)]

def tree_fort_free_nonpure_counterexample_G : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ tree_fort_free_nonpure_counterexample_edges)

instance : DecidableRel tree_fort_free_nonpure_counterexample_G.Adj := by
  intro u v
  dsimp [tree_fort_free_nonpure_counterexample_G, SimpleGraph.fromRel]
  infer_instance

lemma tree_fort_free_nonpure_counterexample_isTree : tree_fort_free_nonpure_counterexample_G.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    use 0
    intro w
    fin_cases w
    · exact SimpleGraph.Reachable.refl 0
    · have h : tree_fort_free_nonpure_counterexample_G.Adj 0 1 := by decide
      exact h.reachable
    · have h01 : tree_fort_free_nonpure_counterexample_G.Adj 0 1 := by decide
      have h12 : tree_fort_free_nonpure_counterexample_G.Adj 1 2 := by decide
      exact h01.reachable.trans h12.reachable
    · have h03 : tree_fort_free_nonpure_counterexample_G.Adj 0 3 := by decide
      exact h03.reachable
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide

theorem tree_fort_free_nonpure_counterexample : ∃ (G : SimpleGraph (Fin 4)) (A B : Finset (Fin 4)), G.IsTree ∧ A.card = 2 ∧ B.card = 3 ∧ is_zero_forcing_set G ((Finset.univ \ A : Finset (Fin 4)) : Set (Fin 4)) ∧ is_zero_forcing_set G ((Finset.univ \ B : Finset (Fin 4)) : Set (Fin 4)) ∧ ∀ x ∉ A, ¬ is_zero_forcing_set G ((Finset.univ \ insert x A : Finset (Fin 4)) : Set (Fin 4)) := by
  refine ⟨tree_fort_free_nonpure_counterexample_G, {2, 3}, {0, 1, 2},
    tree_fort_free_nonpure_counterexample_isTree, by decide, by decide, ?_, ?_, ?_⟩
  · rw [zfs_compl_iff_no_stuck]
    decide
  · rw [zfs_compl_iff_no_stuck]
    decide
  · intro x hx
    rw [zfs_compl_iff_no_stuck]
    fin_cases x
    · decide
    · decide
    · exfalso; apply hx; decide
    · exfalso; apply hx; decide
