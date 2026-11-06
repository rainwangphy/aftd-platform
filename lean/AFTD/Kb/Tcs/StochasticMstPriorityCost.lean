import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstPriorityCostAux

/-!
# stochastic_mst_priority_cost

Topic: algorithms   Node: 5e92e858bdae

Provenance: formalization of a published result. Source: arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 3, ExecuteTutteStrategy(pi); minimizing over pi is the quantity of open problem OP-1209

For a simple graph G on a finite vertex type V with decidable adjacency and p : Sym2 V → ℝ, P(G,p) is the infimum (sInf in ℝ) of the set of values stochastic_mst_priority_cost_aux G p pi (G.edgeFinset.card) ∅ ∅ over all lists pi that are permutations (List.Perm) of G.edgeFinset.toList: the least expected number of queries of a fixed-priority strategy.
-/

noncomputable def stochastic_mst_priority_cost {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : Sym2 V → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ π : List (Sym2 V), π.Perm G.edgeFinset.toList ∧
    x = stochastic_mst_priority_cost_aux G p π G.edgeFinset.card ∅ ∅}
