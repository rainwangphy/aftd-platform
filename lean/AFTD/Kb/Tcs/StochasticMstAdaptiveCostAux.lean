import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstQueryEligible

/-!
# stochastic_mst_adaptive_cost_aux

Topic: algorithms   Node: 3a0e908503fe

Provenance: formalization of a published result. Source: arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Lemma 2.2 (a partial realization certifies an MST iff its minor has only loops and bridges) and Lemmas 3.1-3.2 (an optimal adaptive strategy queries only non-loop non-bridge edges, i.e. is a Tutte strategy): the optimal adaptive cost as a recursion over states

For a simple graph G on a finite vertex type V with decidable adjacency and p : Sym2 V → ℝ (p e the probability that edge e has weight 1), the optimal expected number of further queries from the state (Z, D) of finite edge sets (Finsets of Sym2 V), with fuel k : ℕ: it is 0 when k = 0, and also 0 when no edge of G.edgeFinset satisfies stochastic_mst_query_eligible G Z D; otherwise it is the minimum, over the edges e of G.edgeFinset with stochastic_mst_query_eligible G Z D e, of 1 + p e * value(k-1, Z, insert e D) + (1 - p e) * value(k-1, insert e Z, D).
-/

noncomputable def stochastic_mst_adaptive_cost_aux {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : Sym2 V → ℝ) : ℕ → Finset (Sym2 V) → Finset (Sym2 V) → ℝ := fun
  | 0, _, _ => 0
  | k + 1, Z, D =>
    open Classical in
    if h : (G.edgeFinset.filter (fun e => stochastic_mst_query_eligible G Z D e)).Nonempty then
      (G.edgeFinset.filter (fun e => stochastic_mst_query_eligible G Z D e)).inf' h
        (fun e => 1 + p e * stochastic_mst_adaptive_cost_aux G p k Z (insert e D)
          + (1 - p e) * stochastic_mst_adaptive_cost_aux G p k (insert e Z) D)
    else 0
