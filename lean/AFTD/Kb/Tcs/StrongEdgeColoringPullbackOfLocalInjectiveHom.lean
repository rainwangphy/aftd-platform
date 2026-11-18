import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStrongEdgeColoring

/-!
# strong_edge_coloring_pullback_of_local_injective_hom

Topic: graphs   Node: 76a06bc5ad79

Provenance: helper lemma. The standard graph-cover pullback principle for strong edge colorings; compare https://doi.org/10.1002/jgt.22802.

For simple graphs, a locally injective graph homomorphism pulls back every strong edge coloring of the target to a strong edge coloring of the source.
-/

set_option maxHeartbeats 5000000

theorem strong_edge_coloring_pullback_of_local_injective_hom
    {V W Ω : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hmap : ∀ a b, G.Adj a b → H.Adj (f a) (f b))
    (hinj : ∀ a b c, G.Adj a b → G.Adj a c → f b = f c → b = c)
    (χ : Sym2 W → Ω) (hc : simple_graph_is_strong_edge_coloring H χ) :
    simple_graph_is_strong_edge_coloring G (fun e => χ (Sym2.map f e)) := by
  classical
  intro e he d hd hne hconf
  apply hc (Sym2.map f e) ?_ (Sym2.map f d) ?_ ?_ ?_
  · induction e using Sym2.ind with | _ a b =>
      simpa only [Sym2.map_mk, SimpleGraph.mem_edgeSet] using hmap a b he
  · induction d using Sym2.ind with | _ a b =>
      simpa only [Sym2.map_mk, SimpleGraph.mem_edgeSet] using hmap a b hd
  · revert he hd hne hconf
    induction e using Sym2.ind with | _ a b =>
      induction d using Sym2.ind with | _ c d =>
        intro he hd hne hconf hEq
        simp only [SimpleGraph.mem_edgeSet] at he hd
        simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff] at hEq
        simp only [Sym2.mem_iff] at hconf
        have hnot : ∀ x y, G.Adj x y → f x ≠ f y := fun x y h => H.ne_of_adj (hmap x y h)
        have hes := he.symm
        have hds := hd.symm
        have := fun x y z => hinj x y z
        grind
  · rcases hconf with ⟨a, ha, hb⟩ | ⟨a,b,ha,hb,hab⟩
    · left
      exact ⟨f a, Sym2.mem_map.mpr ⟨a,ha,rfl⟩, Sym2.mem_map.mpr ⟨a,hb,rfl⟩⟩
    · right
      exact ⟨f a,f b,Sym2.mem_map.mpr ⟨a,ha,rfl⟩,Sym2.mem_map.mpr ⟨b,hb,rfl⟩,hmap a b hab⟩
