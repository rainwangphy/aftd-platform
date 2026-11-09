import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphOppositePairStableK4Attachment
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberMono

/-!
# simple_graph_external_k4_private_pair_decreases_packing

Topic: graphs   Node: 2c9485c5b8e1

Provenance: helper lemma. Structural reduction of the pair-stable forced-K4 branch of simple_graph_triangle_cover_number_le_two_mul_packing_number.

Let P be a maximum edge-disjoint triangle packing containing abc, and let a and b occur in no other triangle of P. If x lies outside the vertices of P and abcx is a four-clique, then deleting the opposite edges ab and cx decreases the triangle packing number. No forcing hypothesis is needed.
-/

open scoped Sym2

theorem simple_graph_external_k4_private_pair_decreases_packing (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (a b c x : Fin n) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hx : x ∉ P.biUnion id) (hprivate : ∀ t ∈ P, t ≠ ({a,b,c} : Finset (Fin n)) → a ∉ t ∧ b ∉ t) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b), s(c,x)}) < simple_graph_triangle_packing_number G := by
  classical
  by_contra hn
  have hle : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b), s(c,x)}) ≤
      simple_graph_triangle_packing_number G :=
    simple_graph_triangle_packing_number_mono G _ (SimpleGraph.deleteEdges_le _)
  have hstable : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b), s(c,x)}) =
      simple_graph_triangle_packing_number G := by omega
  have hxnot : ∀ t ∈ P, x ∉ t := by
    intro t ht hxt
    apply hx
    exact Finset.mem_biUnion.mpr ⟨t, ht, hxt⟩
  have hspokes : ∀ t ∈ P, ¬ (x ∈ t ∧ a ∈ t) ∧ ¬ (x ∈ t ∧ b ∈ t) := by
    intro t ht; constructor <;> intro h <;> exact hxnot t ht h.1
  obtain ⟨t, ht, htne, y, hyt, hyout, hatt⟩ :=
    simple_graph_opposite_pair_stable_k4_attachment n G P a b c x htri hdisj hmax hp hk4 hspokes hstable
  rcases hatt with ⟨hab, hxy⟩ | ⟨hxt, hadj⟩
  · have hpv := hprivate t ht htne
    rcases hab with ha | hb
    · exact hpv.1 ha
    · exact hpv.2 hb
  · exact hxnot t ht hxt
