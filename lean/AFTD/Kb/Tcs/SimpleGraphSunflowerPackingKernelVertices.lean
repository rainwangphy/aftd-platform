import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSunflowerPackingWitness

/-!
# simple_graph_sunflower_packing_kernel_vertices

Topic: graphs   Node: 58e2a64b91ad

Provenance: helper lemma. step towards simple_graph_good_sunflower_forced_base_subpacking_kernel_packed

The vertex set W: the endpoints of all petals of Q together with all their witness vertices.
-/

/-- The vertex set of the kernel graph: the endpoints of the petals of Q together with their witness vertices. -/
noncomputable def simple_graph_sunflower_packing_kernel_vertices (n : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n))) (r : Fin n) (Q : Finset (Finset (Fin n))) : Finset (Fin n) := Q.biUnion id ∪ Q.image (fun q => simple_graph_sunflower_packing_witness n G P r q)
