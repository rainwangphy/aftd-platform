import AFTD.Prelude

/-!
# ediam_le_two_of_card_sub_one_le_two_mul_minDegree

Topic: graphs   Node: 0f76115c9ea9

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Lemma 4.1; diameter as Mathlib's extended diameter `ediam`, so the conclusion includes connectedness.

A graph on n vertices with minimum degree δ(G) ≥ (n − 1)/2 has diameter at most 2 (in particular it is connected).
-/

theorem ediam_le_two_of_card_sub_one_le_two_mul_minDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ((Fintype.card V : ℝ) - 1) / 2 ≤ (G.minDegree : ℝ)) : G.ediam ≤ 2 := by
  rw [SimpleGraph.ediam_le_iff]
  intro u v
  by_contra hlt
  rw [not_le, SimpleGraph.two_lt_edist_iff] at hlt
  rcases hlt with ⟨huv, hnotadj, hcn⟩
  have hd1 : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    subst hxy
    rw [SimpleGraph.mem_neighborFinset] at hx hy
    have : x ∈ G.commonNeighbors u v := by
      rw [SimpleGraph.mem_commonNeighbors]
      exact ⟨hx, hy⟩
    rw [hcn] at this
    exact this
  have hd2 : Disjoint (G.neighborFinset u) ({u, v} : Finset V) := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]; exact G.irrefl
    · rw [SimpleGraph.mem_neighborFinset]; exact hnotadj
  have hd3 : Disjoint (G.neighborFinset v) ({u, v} : Finset V) := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]; intro hadj; exact hnotadj hadj.symm
    · rw [SimpleGraph.mem_neighborFinset]; exact G.irrefl
  have hd4 : Disjoint (G.neighborFinset u ∪ G.neighborFinset v) ({u, v} : Finset V) :=
    Finset.disjoint_union_left.mpr ⟨hd2, hd3⟩
  have h_card := Finset.card_le_univ ((G.neighborFinset u ∪ G.neighborFinset v) ∪ {u, v})
  rw [Finset.card_union_of_disjoint hd4, Finset.card_union_of_disjoint hd1] at h_card
  have h_uv : Finset.card ({u, v} : Finset V) = 2 := Finset.card_pair huv
  rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree, h_uv] at h_card
  have hu : G.minDegree ≤ G.degree u := G.minDegree_le_degree u
  have hv : G.minDegree ≤ G.degree v := G.minDegree_le_degree v
  have h_card_real : (G.degree u : ℝ) + (G.degree v : ℝ) + 2 ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast h_card
  have hu_real : (G.minDegree : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hu
  have hv_real : (G.minDegree : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hv
  linarith
