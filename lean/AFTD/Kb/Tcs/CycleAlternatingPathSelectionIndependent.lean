import AFTD.Prelude
import AFTD.Kb.Tcs.AlternatingPathSelectedSet
import AFTD.Kb.Tcs.AlternatingPathSelectedSubsetBIndep

/-!
# cycle_alternating_path_selection_independent

Topic: graphs   Node: c3451fb068f6

Provenance: formalization of a published result. Source: arXiv:2611.06985 Lemma 3.3 -- Every r-regular Hamiltonian graph with r >= 17 contains a second Hamilton cycle

Let C be a simple graph on vertex type V and ρ : V a vertex such that (C.induce ({ρ}ᶜ : Set V)).IsBipartiteWith A B holds for subsets A, B of the subtype {ρ}ᶜ. For any subset T ⊆ B, every pair of vertices u, v in alternating_path_selected_set C ρ A T satisfies ¬ C.Adj u v.
-/

/-- The alternating path selected set S is independent in the cycle graph C. -/
theorem cycle_alternating_path_selection_independent {V : Type*} (C : SimpleGraph V) (ρ : V)
    (A B : Set ({ρ}ᶜ : Set V))
    (h_bip : (C.induce ({ρ}ᶜ : Set V)).IsBipartiteWith A B)
    (T : Set ({ρ}ᶜ : Set V)) (hT : T ⊆ B) :
    ∀ u ∈ alternating_path_selected_set C ρ A T,
    ∀ v ∈ alternating_path_selected_set C ρ A T,
    ¬ C.Adj u v := by
  intro u hu v hv
  simp only [alternating_path_selected_set, Set.mem_union, Set.mem_ofPred_eq] at hu hv
  rintro hadj
  have hG : (C.induce ({ρ}ᶜ : Set V)).Adj u v := SimpleGraph.induce_adj.mpr hadj
  rcases hu with huT | ⟨huA, huP⟩
  · rcases hv with hvT | ⟨hvA, hvP⟩
    · exact alternating_path_selected_subset_b_indep C ρ A B h_bip T hT u huT v hvT hG
    · exact hvP u huT hG.symm
  · rcases hv with hvT | ⟨hvA, hvP⟩
    · exact huP v hvT hG
    · rcases h_bip.mem_of_adj hG with ⟨_, hvB⟩ | ⟨huB, _⟩
      · exact (Set.disjoint_left.1 h_bip.disjoint) hvA hvB
      · exact (Set.disjoint_left.1 h_bip.disjoint) huA huB
