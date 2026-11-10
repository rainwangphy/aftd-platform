import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# finite_vertex_set_edge_encoding_disjoint_iff_inter_card_le_one

Topic: combinatorics   Node: 93985562661a

Provenance: helper lemma. Reusable packing step for simple_graph_forced_k4_face_pivot_retains_forcing.

Two finite vertex sets have disjoint non-diagonal unordered-pair encodings exactly when their intersection contains at most one vertex.
-/

open scoped Sym2
namespace In700Edge
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
lemma in700_encoding_disjoint_iff {V : Type*} [DecidableEq V] (s t : Finset V)
    (h : Disjoint (finite_vertex_set_edge_encoding s) (finite_vertex_set_edge_encoding t)) :
    (s ∩ t).card ≤ 1 := by
  classical
  by_contra hn
  have hh : 1 < (s ∩ t).card := by omega
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hh
  obtain ⟨hus,hut⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvs,hvt⟩ := Finset.mem_inter.mp hv
  have h1 : s(u,v) ∈ finite_vertex_set_edge_encoding s := by
    simp [finite_vertex_set_edge_encoding, hus, hvs, huv]
  have h2 : s(u,v) ∈ finite_vertex_set_edge_encoding t := by
    simp [finite_vertex_set_edge_encoding, hut, hvt, huv]
  exact Finset.disjoint_left.mp h h1 h2
end In700Edge

theorem finite_vertex_set_edge_encoding_disjoint_iff_inter_card_le_one {V : Type*} [DecidableEq V] (s t : Finset V) : Disjoint (finite_vertex_set_edge_encoding s) (finite_vertex_set_edge_encoding t) ↔ (s ∩ t).card ≤ 1 := by
  exact ⟨In700Edge.in700_encoding_disjoint_iff s t, In700Edge.in700_encoding_disjoint s t⟩
