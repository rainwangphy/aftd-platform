import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstAdaptiveCostAux

/-!
# stochastic_mst_adaptive_cost

Topic: algorithms   Node: 589708b440ca

Provenance: formalization of a published result. Source: arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 2-3: the adaptive Stochastic MST-ID problem

For a simple graph G on a finite vertex type V with decidable adjacency and p : Sym2 V → ℝ, A(G,p) := stochastic_mst_adaptive_cost_aux G p applied with fuel G.edgeFinset.card (the number of edges of G) to the empty state Z = ∅, D = ∅: the minimum expected number of edge queries of an adaptive strategy certifying a minimum spanning tree.
-/

noncomputable def stochastic_mst_adaptive_cost {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : Sym2 V → ℝ) : ℝ :=
  stochastic_mst_adaptive_cost_aux G p G.edgeFinset.card ∅ ∅
