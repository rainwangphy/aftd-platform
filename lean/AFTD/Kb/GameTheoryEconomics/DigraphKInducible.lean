import AFTD.Prelude

/-!
# digraph_k_inducible

Topic: social_choice   Node: 1040d23a50cc

Provenance: formalization of a published result. Source: arXiv:2611.27965 (Recognizing k-inducible Digraphs is NP-complete), Section 1: definition of k-inducible digraphs (majority relation of a k-voter preference profile); linear orders encoded by injective rank functions into ℕ

A digraph D on vertex type V is k-inducible (k a natural number) if it is the pairwise majority relation of a profile of k voters with linear orders on V: there are rank functions r_i : V → ℕ for voters i ∈ Fin k, each injective (voter i prefers u to v iff r_i(u) < r_i(v)), such that for all vertices u, v, D has the arc u → v iff strictly more than half of the k voters prefer u to v, i.e. k < 2 · #{i : r_i(u) < r_i(v)}. (In particular D has no loops.)
-/

def digraph_k_inducible (k : ℕ) {V : Type*} (D : Digraph V) : Prop :=
  ∃ r : Fin k → V → ℕ, (∀ i, Function.Injective (r i)) ∧
    ∀ u v, D.Adj u v ↔ k < 2 * (Finset.univ.filter (fun i => r i u < r i v)).card
