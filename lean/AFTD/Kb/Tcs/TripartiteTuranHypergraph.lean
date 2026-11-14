import AFTD.Prelude

/-!
# tripartite_turan_hypergraph

Topic: combinatorics   Node: 32e25c5a32ff

Provenance: formalization of a published result. Source: arXiv:2611.16654 Section 3

Given a type α with decidable equality and a family of finite sets V : ZMod 3 → Finset α, tripartite_turan_hypergraph V is the finite set of 3-element subsets e of the union Finset.univ.biUnion V such that either for all i : ZMod 3, (e ∩ V i).card = 1, or there exists some i : ZMod 3 such that (e ∩ V i).card = 2 and (e ∩ V (i + 1)).card = 1.
-/

/-- The 3-uniform tripartite Turán construction on three parts V₀, V₁, V₂. -/
def tripartite_turan_hypergraph {α : Type*} [DecidableEq α] (V : ZMod 3 → Finset α) :
    Finset (Finset α) := ((Finset.univ.biUnion V).powersetCard 3).filter fun e =>
    (∀ i : ZMod 3, (e ∩ V i).card = 1) ∨
    (∃ i : ZMod 3, (e ∩ V i).card = 2 ∧ (e ∩ V (i + 1)).card = 1)
