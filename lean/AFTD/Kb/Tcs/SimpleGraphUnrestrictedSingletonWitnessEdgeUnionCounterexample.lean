import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_unrestricted_singleton_witness_edge_union_counterexample

Topic: graphs   Node: 3108ce7163b0

Provenance: helper lemma. Counterexample to a misformulated sunflower helper in the triangle-packing campaign; experiment 20269.

The unrestricted witness-edge union does not satisfy the proposed sunflower forced-base half-independence statement: the explicitly quantified statement with that formula has a five-vertex counterexample.
-/

open scoped Sym2
open Finset

def in693_book_E : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(1,2),s(1,3),s(2,3),s(1,4),s(2,4)}
def in693_book_G : SimpleGraph (Fin 5) where
  Adj u v := s(u,v) ∈ in693_book_E ∧ u ≠ v
  symm := ⟨fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.2 rfl⟩
instance : DecidableRel in693_book_G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ in693_book_E ∧ _ ≠ _))
def in693_book_P : Finset (Finset (Fin 5)) := {{0,1,2}}
def in693_book_T : Finset (Finset (Fin 5)) := {{0,1,2},{1,2,3},{1,2,4}}
lemma in693_book_cliques : ∀ t : Finset (Fin 5), in693_book_G.IsNClique 3 t ↔ t ∈ in693_book_T := by decide +kernel
lemma in693_book_packing : simple_graph_triangle_packing_number in693_book_G = 1 := by
  unfold simple_graph_triangle_packing_number
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨in693_book_P, ?_, ?_, ?_⟩ <;> decide +kernel
  · rintro n ⟨T, hT, hpw, rfl⟩
    have hsub : T ⊆ in693_book_T := fun t ht => (in693_book_cliques t).1 (hT t ht)
    by_contra hc
    have htwo : 1 < T.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
    have hp := hpw ha hb hab
    have han : a ∈ in693_book_T := hsub ha
    have hbn : b ∈ in693_book_T := hsub hb
    have hcontra : ∀ a ∈ in693_book_T, ∀ b ∈ in693_book_T, a ≠ b → ¬ (a ∩ b).card ≤ 1 := by decide +kernel
    exact hcontra a han b hbn hab hp
lemma in693_book_family : simple_graph_triangle_edge_family in693_book_G = in693_book_T.image finite_vertex_set_edge_encoding := by
  classical
  ext x
  simp only [simple_graph_triangle_edge_family, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, in693_book_cliques]
lemma in693_book_Pclique : ∀ t ∈ in693_book_P, in693_book_G.IsNClique 3 t := by decide +kernel
lemma in693_book_Pdisj : (in693_book_P : Set (Finset (Fin 5))).Pairwise (fun t u => (t ∩ u).card ≤ 1) := by decide +kernel
lemma in693_book_root : ∀ t ∈ in693_book_P, (0 : Fin 5) ∈ t := by decide +kernel
lemma in693_book_good : ∀ p ∈ in693_book_P, (finite_vertex_set_edge_encoding p ∩ (((simple_graph_triangle_edge_family in693_book_G).filter (fun t => (t ∩ in693_book_P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)).card ≤ 1 := by
  rw [in693_book_family]
  decide +kernel
lemma in693_book_no_Z : ¬ ∃ Z : Finset (Fin 5), Z ⊆ (((((simple_graph_triangle_edge_family in693_book_G).filter (fun t => (t ∩ in693_book_P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id).filter (fun e => (0 : Fin 5) ∉ e.toFinset))).biUnion Sym2.toFinset ∧ (((((simple_graph_triangle_edge_family in693_book_G).filter (fun t => (t ∩ in693_book_P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id).filter (fun e => (0 : Fin 5) ∉ e.toFinset))).card ≤ Z.card := by
  rw [in693_book_family]
  decide +kernel

theorem simple_graph_unrestricted_singleton_witness_edge_union_counterexample : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (r : Fin n) (F : Finset (Sym2 (Fin n))) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hroot : ∀ t ∈ P, r ∈ t) (hgood : ∀ p ∈ P, (finite_vertex_set_edge_encoding p ∩ (((simple_graph_triangle_edge_family G).filter (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)).card ≤ 1) (hF : F = ((((simple_graph_triangle_edge_family G).filter (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id).filter (fun e => r ∉ e.toFinset))), ∃ Z : Finset (Fin n), Z ⊆ F.biUnion Sym2.toFinset ∧ F.card ≤ Z.card ∧ ∀ u ∈ Z, ∀ v ∈ Z, G.Adj u v → s(u,v) ∈ F) := by
  intro h
  let F := (((simple_graph_triangle_edge_family in693_book_G).filter (fun t => (t ∩ in693_book_P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id).filter (fun e => (0 : Fin 5) ∉ e.toFinset)
  have hmax : in693_book_P.card = simple_graph_triangle_packing_number in693_book_G := by rw [in693_book_packing]; decide +kernel
  obtain ⟨Z, hsub, hcard, _⟩ := h 5 in693_book_G in693_book_P 0 F in693_book_Pclique in693_book_Pdisj hmax in693_book_root in693_book_good rfl
  exact in693_book_no_Z ⟨Z, hsub, hcard⟩
