import AFTD.Prelude

/-!
# simple_graph_link_matching_cover_certificate

Topic: graphs   Node: 83f65a5b0bd9

Provenance: helper lemma. arXiv:2610.15269, Section 2, the matching-cover condition for a reducible link.

The graph has a matching M and a vertex set Q of size at most |M| such that all edges avoiding Q belong to M.
-/

def simple_graph_link_matching_cover_certificate {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop := ∃ (M : Finset (Sym2 V)) (Q : Finset V), (∀ e ∈ M, e ∈ G.edgeSet) ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v ∈ e, v ∉ f) ∧ Q.card ≤ M.card ∧ (∀ e ∈ G.edgeSet, (∀ v ∈ Q, v ∉ e) → e ∈ M)
