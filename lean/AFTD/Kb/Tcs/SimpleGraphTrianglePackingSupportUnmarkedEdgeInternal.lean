import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_triangle_packing_support_unmarked_edge_internal

Topic: graphs   Node: 01d4aaea6731

Provenance: helper lemma. Induced-support kernel for the triangle-covering campaign. The proof uses only maximality and singleton forcing; computations 16634–16637 motivated the reduction.

Let U be the edge support of a maximal triangle packing on a vertex set S, and let M contain each support edge that is the only support edge in some triangle. Any triangle through an edge with both endpoints in S and outside M has all its vertices in S.
-/

lemma simple_graph_triangle_packing_support_unmarked_edge_internal_encoding_sub_singleton
    {V : Type*} [DecidableEq V] {A : Finset V} (hA : A.card ≤ 2)
    {e1 e2 : Sym2 V} (h1 : e1 ∈ finite_vertex_set_edge_encoding A)
    (h2 : e2 ∈ finite_vertex_set_edge_encoding A) : e1 = e2 := by
  induction' e1 using Sym2.inductionOn with x1 y1
  induction' e2 using Sym2.inductionOn with x2 y2
  unfold finite_vertex_set_edge_encoding at h1 h2
  simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at h1 h2
  rcases h1 with ⟨⟨hx1, hy1⟩, hne1⟩
  rcases h2 with ⟨⟨hx2, hy2⟩, hne2⟩
  have hsub : ({x1, y1} : Finset V) ⊆ A := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hcard : ({x1, y1} : Finset V).card = 2 := Finset.card_pair hne1
  have heq : ({x1, y1} : Finset V) = A :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hx2' : x2 ∈ ({x1, y1} : Finset V) := heq.symm ▸ hx2
  have hy2' : y2 ∈ ({x1, y1} : Finset V) := heq.symm ▸ hy2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx2' hy2'
  rw [Sym2.eq_iff]
  rcases hx2' with rfl | rfl <;> rcases hy2' with rfl | rfl
  · contradiction
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩
  · contradiction

lemma simple_graph_triangle_packing_support_unmarked_edge_internal_mem_encoding_sdiff_singleton
    {V : Type*} [DecidableEq V]
    {t S : Finset V} {v : V} {e : Sym2 V}
    (het : e ∈ finite_vertex_set_edge_encoding t)
    (heS : e ∈ finite_vertex_set_edge_encoding S)
    (hv : v ∉ S) :
    e ∈ finite_vertex_set_edge_encoding (t \ {v}) := by
  induction' e using Sym2.inductionOn with x y
  unfold finite_vertex_set_edge_encoding at het heS ⊢
  simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at het heS ⊢
  rcases het with ⟨⟨hxt, hyt⟩, hne⟩
  rcases heS with ⟨⟨hxS, hyS⟩, -⟩
  refine ⟨⟨?_, ?_⟩, hne⟩
  · simp only [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hxt, fun h => ?_⟩
    subst h
    exact hv hxS
  · simp only [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hyt, fun h => ?_⟩
    subst h
    exact hv hyS

lemma simple_graph_triangle_packing_support_unmarked_edge_internal_subset_singleton_nonempty_eq
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (hsub : s ⊆ {a}) (hne : s.Nonempty) : s = {a} := by
  ext x
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    exact Finset.mem_singleton.mp (hsub hx)
  · rintro rfl
    rcases hne with ⟨y, hy⟩
    have hy_eq := Finset.mem_singleton.mp (hsub hy)
    rwa [hy_eq] at hy

theorem simple_graph_triangle_packing_support_unmarked_edge_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (U M : Finset (Sym2 V))
    (hU : U ⊆ finite_vertex_set_edge_encoding S)
    (hmax : ∀ t : Finset V, G.IsNClique 3 t →
      (finite_vertex_set_edge_encoding t ∩ U).Nonempty)
    (hforced : ∀ t : Finset V, G.IsNClique 3 t →
      (finite_vertex_set_edge_encoding t ∩ U).card = 1 →
      finite_vertex_set_edge_encoding t ∩ U ⊆ M) :
    ∀ t : Finset V, G.IsNClique 3 t → ∀ e ∈ finite_vertex_set_edge_encoding t,
      e ∈ finite_vertex_set_edge_encoding S → e ∉ M → t ⊆ S := by
  intro t ht e het heS heM
  by_contra hnot
  rcases Finset.not_subset.mp hnot with ⟨v, hvt, hvS⟩
  have he_A : e ∈ finite_vertex_set_edge_encoding (t \ {v}) :=
    simple_graph_triangle_packing_support_unmarked_edge_internal_mem_encoding_sdiff_singleton
      het heS hvS
  have hA_card : (t \ {v}).card ≤ 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hvt, ht.card_eq]
  have hsub_e : finite_vertex_set_edge_encoding t ∩ U ⊆ {e} := by
    intro e' he'
    rw [Finset.mem_inter] at he'
    have he'_S : e' ∈ finite_vertex_set_edge_encoding S := hU he'.2
    have he'_A : e' ∈ finite_vertex_set_edge_encoding (t \ {v}) :=
      simple_graph_triangle_packing_support_unmarked_edge_internal_mem_encoding_sdiff_singleton
        he'.1 he'_S hvS
    have he'_eq_e : e' = e :=
      simple_graph_triangle_packing_support_unmarked_edge_internal_encoding_sub_singleton
        hA_card he'_A he_A
    exact Finset.mem_singleton.mpr he'_eq_e
  have h_ne : (finite_vertex_set_edge_encoding t ∩ U).Nonempty := hmax t ht
  have heq : finite_vertex_set_edge_encoding t ∩ U = {e} :=
    simple_graph_triangle_packing_support_unmarked_edge_internal_subset_singleton_nonempty_eq
      hsub_e h_ne
  have hcard : (finite_vertex_set_edge_encoding t ∩ U).card = 1 := by
    rw [heq, Finset.card_singleton]
  have hM_sub : finite_vertex_set_edge_encoding t ∩ U ⊆ M :=
    hforced t ht hcard
  have heM' : e ∈ M := by
    apply hM_sub
    rw [heq]
    exact Finset.mem_singleton_self e
  exact heM heM'
