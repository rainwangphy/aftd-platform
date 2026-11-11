import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_triangle_packing_number_ge_of_edge_reduction

Topic: graphs   Node: 2d75a9e0587f

Provenance: helper lemma. arXiv:2611.11128 Lemma 2.2 -- Triangle-overlap cores and density bounds for Tuza's conjecture

Let G be a finite simple graph, F a nonempty edge subset, S a pairwise edge-disjoint triangle family, and X an edge subset such that X meets every triangle containing an edge of F and E(S) \ F ⊆ X. Then the triangle packing number of G \ (F ∪ X) plus |S| is at most the triangle packing number of G.
-/

open Classical

def simple_graph_triangle_packing_number_ge_of_edge_reduction.feasible
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset (Finset V)) : Prop :=
  (∀ t ∈ T, G.IsNClique 3 t) ∧ ((T : Set (Finset V)).Pairwise fun s t => (s ∩ t).card ≤ 1)

lemma simple_graph_triangle_packing_number_ge_of_edge_reduction.feasible_eq
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    simple_graph_triangle_packing_number G
      = sSup {n : ℕ | ∃ T, feasible G T ∧ T.card = n} := by
  simp only [simple_graph_triangle_packing_number, feasible, and_assoc]

lemma simple_graph_triangle_packing_number_ge_of_edge_reduction.bddAbove
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    BddAbove {n : ℕ | ∃ T, feasible G T ∧ T.card = n} := by
  refine ⟨(Finset.univ.powerset : Finset (Finset V)).card, ?_⟩
  rintro n ⟨T, hT, rfl⟩
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_powerset]
  exact Finset.subset_univ x

lemma simple_graph_triangle_packing_number_ge_of_edge_reduction.nonempty
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    ({n : ℕ | ∃ T, feasible G T ∧ T.card = n} : Set ℕ).Nonempty := by
  refine ⟨0, ∅, ?_, by simp⟩
  simp [feasible]

lemma simple_graph_triangle_packing_number_ge_of_edge_reduction.card_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (T : Finset (Finset V)) (h : feasible G T) :
    T.card ≤ simple_graph_triangle_packing_number G := by
  rw [feasible_eq]
  exact le_csSup (bddAbove G) ⟨T, h, rfl⟩

lemma simple_graph_triangle_packing_number_ge_of_edge_reduction.exists_packing
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ T, feasible G T ∧ T.card = simple_graph_triangle_packing_number G := by
  rw [feasible_eq]
  exact Nat.sSup_mem (nonempty G) (bddAbove G)

open Classical in
/-- Under an edge reduction (F, S, X), the triangle packing number of G is at least that of G \ (F ∪ X) plus |S|. -/
theorem simple_graph_triangle_packing_number_ge_of_edge_reduction
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) (hFne : F.Nonempty)
    (S : Finset (Finset V)) (hS : ∀ t ∈ S, G.IsNClique 3 t)
    (hSpairwise : (S : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1))
    (X : Finset (Sym2 V)) (hX : X ⊆ G.edgeFinset)
    (hXmeets : ∀ t : Finset V, G.IsNClique 3 t →
      (∃ e ∈ F, ∀ x ∈ e, x ∈ t) → ∃ e ∈ X, ∀ x ∈ e, x ∈ t)
    (hES : (S.biUnion finite_vertex_set_edge_encoding \ F) ⊆ X) :
    simple_graph_triangle_packing_number (G.deleteEdges (↑(F ∪ X) : Set (Sym2 V))) + S.card ≤
      simple_graph_triangle_packing_number G := by
  obtain ⟨T0, hT0, hT0card⟩ :=
    simple_graph_triangle_packing_number_ge_of_edge_reduction.exists_packing
      (G.deleteEdges (↑(F ∪ X) : Set (Sym2 V)))
  have hcross : ∀ t ∈ T0, ∀ s ∈ S, (t ∩ s).card ≤ 1 := by
    intro t ht s hs
    by_contra hle
    rw [not_le] at hle
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hle
    rw [Finset.mem_inter] at ha hb
    have hadj' : (G.deleteEdges (↑(F ∪ X) : Set (Sym2 V))).Adj a b :=
      (hT0.1 t ht).isClique ha.1 hb.1 hab
    have hadj : G.Adj a b := (hS s hs).isClique ha.2 hb.2 hab
    have he'_edge : s(a, b) ∈ (G.deleteEdges (↑(F ∪ X) : Set (Sym2 V))).edgeSet :=
      (SimpleGraph.mem_edgeSet (G.deleteEdges (↑(F ∪ X) : Set (Sym2 V)))).mpr hadj'
    rw [SimpleGraph.edgeSet_deleteEdges] at he'_edge
    have he_notin : s(a, b) ∉ F ∪ X := fun hmem => he'_edge.2 (by simpa using hmem)
    have he_enc : s(a, b) ∈ finite_vertex_set_edge_encoding s := by
      rw [finite_vertex_set_edge_encoding, Finset.mem_filter]
      exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨ha.2, hb.2⟩, by rwa [Sym2.mk_isDiag_iff]⟩
    have he_bi : s(a, b) ∈ S.biUnion finite_vertex_set_edge_encoding :=
      Finset.mem_biUnion.mpr ⟨s, hs, he_enc⟩
    have heFX : s(a, b) ∈ F ∪ X := by
      by_cases heF : s(a, b) ∈ F
      · exact Finset.mem_union.mpr (Or.inl heF)
      · exact Finset.mem_union.mpr (Or.inr (hES (Finset.mem_sdiff.mpr ⟨he_bi, heF⟩)))
    exact he_notin heFX
  have hdisj : Disjoint T0 S := by
    rw [Finset.disjoint_left]
    intro s hsT hsS
    have h1 := hcross s hsT s hsS
    rw [Finset.inter_self] at h1
    have h2 : s.card = 3 := (hS s hsS).card_eq
    omega
  have hunion : simple_graph_triangle_packing_number_ge_of_edge_reduction.feasible G (T0 ∪ S) := by
    constructor
    · intro t ht
      rw [Finset.mem_union] at ht
      rcases ht with ht | ht
      · exact (hT0.1 t ht).mono (SimpleGraph.deleteEdges_le (↑(F ∪ X) : Set (Sym2 V)))
      · exact hS t ht
    · rw [Finset.coe_union, Set.pairwise_union]
      refine ⟨hT0.2, hSpairwise, ?_⟩
      intro a ha b hb hab
      exact ⟨hcross a ha b hb, by rw [Finset.inter_comm]; exact hcross a ha b hb⟩
  have hcard : (T0 ∪ S).card = T0.card + S.card := Finset.card_union_of_disjoint hdisj
  have hle : (T0 ∪ S).card ≤ simple_graph_triangle_packing_number G :=
    simple_graph_triangle_packing_number_ge_of_edge_reduction.card_le G (T0 ∪ S) hunion
  rw [hcard, hT0card] at hle
  exact hle
