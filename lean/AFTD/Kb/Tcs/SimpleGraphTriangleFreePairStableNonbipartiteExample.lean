import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberMono
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberEqZeroOfCliqueFree
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_free_pair_stable_nonbipartite_example

Topic: graphs   Node: 90f920c38411

Provenance: helper lemma. A five-cycle refutes the unrestricted unpacked-edge bipartiteness shortcut; compare experiment 20873.

A triangle-free two-edge-stable graph can fail to be bipartite; its empty packing is maximum and support-maximal.
-/

open scoped Sym2
namespace In701Odd

def E : Finset (Sym2 (Fin 5)) := {s(0,1),s(1,2),s(2,3),s(3,4),s(4,0)}
def G : SimpleGraph (Fin 5) where
  Adj u v := s(u,v) ∈ E ∧ u ≠ v
  symm := ⟨fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.2 rfl⟩
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ E ∧ _ ≠ _))

theorem no_triangle : G.CliqueFree 3 := by
  have h : ∀ t ∈ (Finset.univ : Finset (Fin 5)).powersetCard 3, ¬ G.IsNClique 3 t := by decide +kernel
  intro t ht
  exact h t (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,ht.card_eq⟩) ht
theorem no_coloring : ∀ f : Fin 5 → Bool, ∃ u v, G.Adj u v ∧ f u = f v := by decide +kernel

theorem packing_zero : simple_graph_triangle_packing_number G = 0 :=
  simple_graph_triangle_packing_number_eq_zero_of_clique_free G no_triangle

theorem stable : ∀ e f : Sym2 (Fin 5), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
    simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G := by
  intro e f _ _ _
  have h := simple_graph_triangle_packing_number_mono G (G.deleteEdges {e,f}) (SimpleGraph.deleteEdges_le _)
  rw [packing_zero] at h ⊢
  omega
end In701Odd

theorem simple_graph_triangle_free_pair_stable_nonbipartite_example : ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧
    (∀ e f : Sym2 (Fin 5), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) ∧
    (∀ f : Fin 5 → Bool, ∃ u v, G.Adj u v ∧ f u = f v) := by
  exact ⟨In701Odd.G,In701Odd.no_triangle,In701Odd.stable,In701Odd.no_coloring⟩
