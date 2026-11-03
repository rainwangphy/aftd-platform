import AFTD.Prelude

/-!
# digraph_local_source_set

Topic: graphs   Node: 19caa5ba47e8

Provenance: helper lemma. arXiv:2601.11847, Problem 5.2 and Proposition 2.3; a local-obstruction construction used in the OP-337 campaign.

Given finite out-neighborhood sets and a vertex v, the vertices outside the closed out-neighborhood of v that have no in-neighbor outside that closed neighborhood.
-/

def digraph_local_source_set {α : Type} [Fintype α] [DecidableEq α]
    (out : α → Finset α) (v : α) : Finset α :=
  Finset.univ.filter fun u => u ≠ v ∧ u ∉ out v ∧
    ∀ p, p ≠ v → p ∉ out v → u ∉ out p
