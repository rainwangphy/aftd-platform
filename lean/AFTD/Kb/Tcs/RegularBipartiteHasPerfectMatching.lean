import AFTD.Prelude

/-!
# regular_bipartite_has_perfect_matching

Topic: graphs   Node: c24ff2f70cd3

Provenance: formalization of a published result. Source: Diestel, Graph Theory, Corollary 2.1.3

Every d-regular bipartite simple graph on a finite vertex set, with degree d > 0, has a perfect matching.
-/

open scoped Classical
open SimpleGraph Finset Set

lemma regular_bipartite_has_perfect_matching_card_le_card_biUnion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d)
    (hreg : G.IsRegularOfDegree d) (S : Finset V) :
    #S ≤ #(S.biUnion (fun x => G.neighborFinset x)) := by
  let T := S.biUnion (fun x => G.neighborFinset x)
  have h_deg (v : V) : #(G.neighborFinset v) = d := by
    rw [card_neighborFinset_eq_degree]
    exact hreg v
  have h_above (u : V) (hu : u ∈ S) : #(bipartiteAbove G.Adj T u) = d := by
    have : bipartiteAbove G.Adj T u = G.neighborFinset u := by
      ext v
      simp only [bipartiteAbove, mem_filter, mem_neighborFinset]
      constructor
      · intro ⟨_, hadj⟩
        exact hadj
      · intro hadj
        refine ⟨?_, hadj⟩
        rw [Finset.mem_biUnion]
        exact ⟨u, hu, G.mem_neighborFinset u v |>.mpr hadj⟩
    rw [this, h_deg]
  have h_below (v : V) : #(bipartiteBelow G.Adj S v) ≤ d := by
    have : bipartiteBelow G.Adj S v ⊆ G.neighborFinset v := by
      intro u hu
      simp only [bipartiteBelow, mem_filter] at hu
      simp only [mem_neighborFinset]
      exact hu.2.symm
    exact (Finset.card_le_card this).trans (h_deg v).le
  have h_sum_above : ∑ u ∈ S, #(bipartiteAbove G.Adj T u) = #S * d := by
    rw [sum_congr rfl h_above]
    simp
  have h_sum_below : ∑ v ∈ T, #(bipartiteBelow G.Adj S v) ≤ #T * d := by
    calc ∑ v ∈ T, #(bipartiteBelow G.Adj S v)
      _ ≤ ∑ v ∈ T, d := sum_le_sum fun v _ => h_below v
      _ = #T * d := by simp
  have h_eq := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s := S) (t := T)
  have h_mul_le : #S * d ≤ #T * d := by
    rw [← h_sum_above, h_eq]
    exact h_sum_below
  exact Nat.le_of_mul_le_mul_right h_mul_le hd

lemma regular_bipartite_has_perfect_matching_ncard_le_ncard_biUnion {V : Type*} [Fintype V]
    (G : SimpleGraph V) {d : ℕ} (hd : 0 < d)
    (hreg : G.IsRegularOfDegree d) (s : Set V) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  have h_eq : (⋃ x ∈ s, G.neighborSet x).toFinset = s.toFinset.biUnion (fun x => G.neighborFinset x) := by
    ext v
    simp
  rw [Set.ncard_eq_toFinset_card' s, Set.ncard_eq_toFinset_card' _, h_eq]
  exact regular_bipartite_has_perfect_matching_card_le_card_biUnion G hd hreg s.toFinset

/-- Every d-regular bipartite graph with d > 0 has a perfect matching. -/
theorem regular_bipartite_has_perfect_matching {V : Type*} [Fintype V]
    (G : SimpleGraph V) {d : ℕ} (hd : 0 < d)
    (hreg : G.IsRegularOfDegree d) (hbip : G.IsBipartite) :
    ∃ M : SimpleGraph.Subgraph G, M.IsPerfectMatching := by
  obtain ⟨p₁, p₂, hbipW⟩ := hbip.exists_isBipartiteWith
  exact exists_isPerfectMatching_of_forall_ncard_le hbipW
    (fun s => regular_bipartite_has_perfect_matching_ncard_le_ncard_biUnion G hd hreg s)
