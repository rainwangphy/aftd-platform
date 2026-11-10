import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# finite_packing_k4_old_edges_avoid

Topic: combinatorics   Node: 1f7f3ee81fc0

Provenance: helper lemma. Core packing reduction in simple_graph_forced_k4_face_pivot_retains_forcing.

For an edge-disjoint family containing abc whose union avoids the three spokes from x, removing abc leaves a family whose encoded edges avoid every edge among a,b,c,x.
-/

open scoped Sym2
namespace In700Old
lemma in700_encoding_disjoint {V : Type*} [DecidableEq V] (s t : Finset V)
    (h : (s ∩ t).card ≤ 1) :
    Disjoint (finite_vertex_set_edge_encoding s) (finite_vertex_set_edge_encoding t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hes het
  induction e using Sym2.ind with
  | _ u v =>
    simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.isDiag_iff_proj_eq] at hes het
    have hm : u ∈ s ∩ t := Finset.mem_inter.mpr ⟨hes.1.1,het.1.1⟩
    have hn : v ∈ s ∩ t := Finset.mem_inter.mpr ⟨hes.1.2,het.1.2⟩
    have hne : u ≠ v := hes.2
    have hh : 1 < (s ∩ t).card := Finset.one_lt_card.mpr ⟨u,hm,v,hn,hne⟩
    omega
lemma in700_four_edges_subset {V : Type*} [DecidableEq V] (a b c x : V) :
    finite_vertex_set_edge_encoding ({a,b,c,x} : Finset V) ⊆
      finite_vertex_set_edge_encoding ({a,b,c} : Finset V) ∪ {s(a,x),s(b,x),s(c,x)} := by
  classical
  intro z hz
  induction z using Sym2.ind with
  | _ u v =>
    simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.mk_isDiag_iff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
      Sym2.eq_iff] at hz ⊢
    aesop
lemma in700_old_edges_disjoint_four {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V)) (a b c x : V)
    (hdisj : (P : Set (Finset V)).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hp : ({a,b,c} : Finset V) ∈ P)
    (hfree : ∀ e ∈ ({s(a,x),s(b,x),s(c,x)} : Finset (Sym2 V)),
      e ∉ P.biUnion finite_vertex_set_edge_encoding) :
    Disjoint (finite_vertex_set_edge_encoding ({a,b,c,x} : Finset V))
      ((P.erase {a,b,c}).biUnion finite_vertex_set_edge_encoding) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hU
  obtain ⟨q,hq,hzq⟩ := Finset.mem_biUnion.mp hU
  obtain ⟨hneq,hqP⟩ := Finset.mem_erase.mp hq
  have hor := in700_four_edges_subset a b c x hz
  rcases Finset.mem_union.mp hor with hzold | hzspoke
  · have hd := in700_encoding_disjoint q {a,b,c} (hdisj hqP hp hneq)
    exact Finset.disjoint_left.mp hd hzq hzold
  · apply hfree z hzspoke
    exact Finset.mem_biUnion.mpr ⟨q,hqP,hzq⟩
end In700Old

theorem finite_packing_k4_old_edges_avoid {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V)) (a b c x : V)
    (hdisj : (P : Set (Finset V)).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hp : ({a,b,c} : Finset V) ∈ P)
    (hfree : ∀ e ∈ ({s(a,x),s(b,x),s(c,x)} : Finset (Sym2 V)),
      e ∉ P.biUnion finite_vertex_set_edge_encoding) :
    Disjoint (finite_vertex_set_edge_encoding ({a,b,c,x} : Finset V))
      ((P.erase {a,b,c}).biUnion finite_vertex_set_edge_encoding) := by
  exact In700Old.in700_old_edges_disjoint_four P a b c x hdisj hp hfree
