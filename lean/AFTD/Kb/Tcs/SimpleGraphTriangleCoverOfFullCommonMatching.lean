import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphMatchingLinkStarPacking
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverOfTwoStarPackings

/-!
# simple_graph_triangle_cover_of_full_common_matching

Topic: graphs   Node: 17f50a2dc75d

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

If an edge common-neighbor graph has a matching as large as the graph triangle packing number, the triangle cover number is at most the packing number plus one.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_triangle_cover_of_full_common_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (M : Finset (Finset V))
    (huv : G.Adj u v)
    (hM : ∀ e ∈ M, e.card = 2 ∧ (∀ x ∈ e, G.Adj u x ∧ G.Adj v x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y))
    (hdis : (M : Set (Finset V)).Pairwise Disjoint)
    (hnum : simple_graph_triangle_packing_number G = M.card) :
    simple_graph_triangle_cover_number G ≤ M.card + 1 := by
  classical
  letI : Nonempty V := ⟨u⟩
  have hrep : ∀ e ∈ M, ∃ a b : V, a ≠ b ∧ e = {a,b} := by
    intro e he
    exact Finset.card_eq_two.mp (hM e he).1
  choose! a b hab heq using hrep
  let C : Finset (Sym2 V) := M.image (fun e => s(a e,b e))
  have hC : ∀ e ∈ C, e ∈ G.edgeSet := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    apply (hM e he).2.2 (a e) ?_ (b e) ?_ (hab e he)
    · have hmem : a e ∈ ({a e, b e} : Finset V) := by simp
      rw [← heq e he] at hmem
      exact hmem
    · have hmem : b e ∈ ({a e, b e} : Finset V) := by simp
      rw [← heq e he] at hmem
      exact hmem
  have hpair : ∀ e ∈ M, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → s(x,y) ∈ C := by
    intro e he x hx y hy hxy
    have hx' : x = a e ∨ x = b e := by
      have hh : x ∈ ({a e,b e} : Finset V) := by rw [← heq e he]; exact hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    have hy' : y = a e ∨ y = b e := by
      have hh : y ∈ ({a e,b e} : Finset V) := by rw [← heq e he]; exact hy
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    have hmem : s(a e,b e) ∈ C := Finset.mem_image.mpr ⟨e, he, rfl⟩
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact (hxy rfl).elim
    · exact hmem
    · simpa [Sym2.eq_swap] using hmem
    · exact (hxy rfl).elim
  have hstar : ∀ z : V, ∀ s ∈ M.image (fun e => insert z e),
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x = z ∨ y = z ∨ s(x,y) ∈ C := by
    intro z s hs x hx y hy hxy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases hy with rfl | hy
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hpair e he x hx y hy hxy))
  have huM : ∀ e ∈ M, e.card = 2 ∧ (∀ x ∈ e, G.Adj u x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y) := by
    intro e he
    exact ⟨(hM e he).1, (fun x hx => ((hM e he).2.1 x hx).1), (hM e he).2.2⟩
  have hvM : ∀ e ∈ M, e.card = 2 ∧ (∀ x ∈ e, G.Adj v x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y) := by
    intro e he
    exact ⟨(hM e he).1, (fun x hx => ((hM e he).2.1 x hx).2), (hM e he).2.2⟩
  have huP := simple_graph_matching_link_star_packing G u M huM hdis
  have hvP := simple_graph_matching_link_star_packing G v M hvM hdis
  have huMax := simple_graph_maximum_triangle_packing_edge_meets G _ huP.1 huP.2.1
    (by rw [huP.2.2, hnum])
  have hvMax := simple_graph_maximum_triangle_packing_edge_meets G _ hvP.1 hvP.2.1
    (by rw [hvP.2.2, hnum])
  have hcover := simple_graph_triangle_cover_of_two_star_packings G u v _ _ C huv hC
    huMax hvMax (hstar u) (hstar v)
  have hcard : C.card ≤ M.card := Finset.card_image_le
  omega
