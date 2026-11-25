import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphOppositePairStableK4Attachment

/-!
# simple_graph_opposite_pair_stable_external_k4_attachment

Topic: graphs   Node: 5c2b8bfb9e9c

Provenance: helper lemma. Structural reduction of the pair-stable forced-K4 branch of simple_graph_triangle_cover_number_le_two_mul_packing_number.

Let P be a maximum edge-disjoint triangle packing containing abc, and let x outside its vertex support complete abc to a four-clique. If deleting the opposite edges ab and cx preserves the packing number, then another triangle of P contains a or b and a vertex y outside abc that is adjacent to x.
-/

open scoped Sym2

theorem simple_graph_opposite_pair_stable_external_k4_attachment (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (a b c x : Fin n) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hx : x ∉ P.biUnion id) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) (hstable : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b), s(c,x)}) = simple_graph_triangle_packing_number G) : ∃ t ∈ P, t ≠ ({a,b,c} : Finset (Fin n)) ∧ (a ∈ t ∨ b ∈ t) ∧ ∃ y ∈ t, y ∉ ({a,b,c} : Finset (Fin n)) ∧ G.Adj x y := by
  have hxnot : ∀ t ∈ P, x ∉ t := by
    intro t ht hxt
    apply hx
    exact Finset.mem_biUnion.mpr ⟨t, ht, hxt⟩
  have hspokes : ∀ t ∈ P, ¬ (x ∈ t ∧ a ∈ t) ∧ ¬ (x ∈ t ∧ b ∈ t) := by
    intro t ht
    constructor <;> intro h <;> exact hxnot t ht h.1
  obtain ⟨t, ht, htne, y, hyt, hyout, hatt⟩ :=
    simple_graph_opposite_pair_stable_k4_attachment n G P a b c x htri hdisj hmax hp hk4 hspokes hstable
  rcases hatt with ⟨hab, hxy⟩ | ⟨hxt, -⟩
  · refine ⟨t, ht, htne, hab, y, hyt, ?_, hxy⟩
    intro hy
    apply hyout
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact False.elim (hxnot t ht hxt)
