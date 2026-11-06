import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstQueryEligible

/-!
# stochastic_mst_priority_cost_aux

Topic: algorithms   Node: b64ae88a51a1

Provenance: formalization of a published result. Source: arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 3, ExecuteTutteStrategy(pi): query edges in the order pi, skipping those that are loops or bridges of the current minor

For a simple graph G on a finite vertex type V with decidable adjacency, p : Sym2 V → ℝ and a list pi of edges (List (Sym2 V)), the expected number of further queries of the priority strategy for pi from the state (Z, D) of finite edge sets (Finsets of Sym2 V), with fuel k : ℕ: it is 0 when k = 0, and also 0 when no element of pi satisfies stochastic_mst_query_eligible G Z D; otherwise, for e the first element of pi (List.find?) with stochastic_mst_query_eligible G Z D e, it is 1 + p e * value(k-1, Z, insert e D) + (1 - p e) * value(k-1, insert e Z, D).
-/

noncomputable def stochastic_mst_priority_cost_aux {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : Sym2 V → ℝ) (π : List (Sym2 V)) :
    ℕ → Finset (Sym2 V) → Finset (Sym2 V) → ℝ := fun
  | 0, _, _ => 0
  | k + 1, Z, D =>
    open Classical in
    match π.find? (fun e => decide (stochastic_mst_query_eligible G Z D e)) with
    | none => 0
    | some e => 1 + p e * stochastic_mst_priority_cost_aux G p π k Z (insert e D)
        + (1 - p e) * stochastic_mst_priority_cost_aux G p π k (insert e Z) D
