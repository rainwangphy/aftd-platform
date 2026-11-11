import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeGraph
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.TenVertexExchangeFamily
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamilyMem
import AFTD.Kb.Tcs.SimpleGraphTwoEdgeStableConnectedFamilyExchangeTrapCounterexample
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TenVertexExchangeEdges

/-!
# ten_vertex_exchange_family_eq

Topic: graphs   Node: 575f4a1fd91d

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The 52 explicit triangle edge sets are exactly the triangle family of the ten-vertex graph.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open scoped Sym2
namespace In732Family
instance in732_G_dec : DecidableRel ten_vertex_exchange_graph.Adj := fun a b =>
  inferInstanceAs (Decidable (s(a,b) ∈ ten_vertex_exchange_edges ∧ a ≠ b))

def in732_tris : List (Fin 10 × Fin 10 × Fin 10) := [(0, 1, 2), (0, 1, 3), (0, 1, 7), (0, 2, 3), (0, 2, 7), (0, 2, 8), (0, 2, 9), (0, 3, 6), (0, 3, 7), (0, 3, 9), (0, 6, 7), (0, 6, 8), (0, 6, 9), (0, 7, 8), (0, 8, 9), (1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 2, 7), (1, 3, 4), (1, 3, 5), (1, 3, 7), (1, 4, 5), (1, 4, 7), (2, 3, 4), (2, 3, 5), (2, 3, 7), (2, 3, 9), (2, 4, 5), (2, 4, 7), (2, 4, 8), (2, 5, 8), (2, 5, 9), (2, 7, 8), (2, 8, 9), (3, 4, 5), (3, 4, 6), (3, 4, 7), (3, 5, 6), (3, 5, 9), (3, 6, 7), (3, 6, 9), (4, 5, 6), (4, 5, 8), (4, 6, 7), (4, 6, 8), (4, 7, 8), (5, 6, 8), (5, 6, 9), (5, 8, 9), (6, 7, 8), (6, 8, 9)]

def in732_enc (x : Fin 10 × Fin 10 × Fin 10) : Finset (Sym2 (Fin 10)) :=
  {s(x.1,x.2.1),s(x.1,x.2.2),s(x.2.1,x.2.2)}

def in732_sort3 (a b c : Fin 10) : Fin 10 × Fin 10 × Fin 10 :=
  if a < b then (if b < c then (a,b,c) else if a < c then (a,c,b) else (c,a,b))
  else (if a < c then (b,a,c) else if b < c then (b,c,a) else (c,b,a))

theorem in732_sort_mem (a : Fin 10) : ∀ b c : Fin 10, ten_vertex_exchange_graph.Adj a b → ten_vertex_exchange_graph.Adj a c → ten_vertex_exchange_graph.Adj b c → in732_sort3 a b c ∈ in732_tris := by
  fin_cases a <;> decide


theorem in732_enc_sort3 (a b c : Fin 10) : in732_enc (in732_sort3 a b c) = {s(a,b),s(a,c),s(b,c)} := by
  unfold in732_sort3 in732_enc
  split_ifs <;> ext e <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> constructor <;> rintro (h | h | h) <;> subst h <;> simp [Sym2.eq_swap]

theorem in732_list_tri : ∀ x ∈ in732_tris, x.1 < x.2.1 ∧ x.2.1 < x.2.2 ∧ ten_vertex_exchange_graph.Adj x.1 x.2.1 ∧ ten_vertex_exchange_graph.Adj x.1 x.2.2 ∧ ten_vertex_exchange_graph.Adj x.2.1 x.2.2 := by
  intro x hx
  simp only [in732_tris, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst x <;> decide

theorem in732_list_family : (in732_tris.map in732_enc).toFinset = ten_vertex_exchange_family := by decide

end In732Family
open In732Family

theorem ten_vertex_exchange_family_eq : simple_graph_triangle_edge_family ten_vertex_exchange_graph = ten_vertex_exchange_family := by
  classical
  rw [← in732_list_family]
  ext t
  rw [simple_graph_triangle_edge_family_mem]
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hs.card_eq
    obtain ⟨h1,h2,h3⟩ := (SimpleGraph.is3Clique_triple_iff).mp hs
    exact ⟨_, in732_sort_mem a b c h1 h2 h3, by
      rw [in732_enc_sort3, ts18_fvsee_triple a b c hab hac hbc]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨l1,l2,h1,h2,h3⟩ := in732_list_tri x hx
    refine ⟨{x.1,x.2.1,x.2.2}, (SimpleGraph.is3Clique_triple_iff).mpr ⟨h1,h2,h3⟩, ?_⟩
    rw [ts18_fvsee_triple _ _ _ (ne_of_lt l1) (ne_of_lt (l1.trans l2)) (ne_of_lt l2)]
    rfl
