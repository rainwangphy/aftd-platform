import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyArrows

/-!
# simple_graph_size_ramsey

Topic: graphs   Node: 784baa6ee758

Provenance: formalization of a published result. Source: arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Section 1: definition of the size Ramsey number

The size Ramsey number r̂(F, H) = min{e(G) : G → (F, H)} over finite graphs G, taken here as graphs on Fin k; every finite graph is isomorphic to one of these. It is 0 if no such G exists.
-/

noncomputable def simple_graph_size_ramsey {α β : Type*} (F : SimpleGraph α)
    (H : SimpleGraph β) : ℕ :=
  sInf {m | ∃ (k : ℕ) (G : SimpleGraph (Fin k)), G.edgeSet.ncard = m ∧
    simple_graph_size_ramsey_arrows G F H}
