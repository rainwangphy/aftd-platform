import AFTD.Prelude

/-!
# alternating_path_selected_subset_b_indep

Topic: graphs   Node: d2273fb4b0a8

Provenance: helper lemma. arXiv:2611.06985 Lemma 3.3 proof step 2

If the induced graph C[{ρ}ᶜ] is bipartite with parts A and B, then any subset T ⊆ B is an independent set in C[{ρ}ᶜ].
-/

/-- In a bipartite graph on {ρ}ᶜ with parts A and B, any subset T ⊆ B is an independent set. -/
theorem alternating_path_selected_subset_b_indep {V : Type*} (C : SimpleGraph V) (ρ : V)
    (A B : Set ({ρ}ᶜ : Set V))
    (h_bip : (C.induce ({ρ}ᶜ : Set V)).IsBipartiteWith A B)
    (T : Set ({ρ}ᶜ : Set V)) (hT : T ⊆ B) :
    ∀ u ∈ T, ∀ v ∈ T, ¬ (C.induce ({ρ}ᶜ : Set V)).Adj u v := by
  intro u hu v hv hadj
  have huB : u ∈ B := hT hu
  have hvB : v ∈ B := hT hv
  rcases h_bip.mem_of_adj hadj with ⟨huA, -⟩ | ⟨-, hvA⟩
  · exact Set.disjoint_left.mp h_bip.disjoint huA huB
  · exact Set.disjoint_right.mp h_bip.disjoint hvB hvA
