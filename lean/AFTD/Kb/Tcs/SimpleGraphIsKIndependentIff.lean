import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# simple_graph_is_k_independent_iff

Topic: graphs   Node: 1f2dd9129cde

Provenance: helper lemma. Computable form of k-independence for arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination) (used for Proposition 7.1 and Theorem 3.2).

With decidable adjacency, a vertex set I is k-independent iff every v ∈ I has fewer than k neighbours in the finset I.filter (G.Adj v).
-/

theorem simple_graph_is_k_independent_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (I : Finset V) :
    simple_graph_is_k_independent G k I ↔ ∀ v ∈ I, (I.filter (G.Adj v)).card < k := open Finset in by
  unfold simple_graph_is_k_independent
  have : ∀ v, ({u | u ∈ I ∧ G.Adj v u} : Set V).ncard = (I.filter (G.Adj v)).card := by
    intro v
    rw [← Set.ncard_coe_finset, coe_filter]
  simp only [this]
