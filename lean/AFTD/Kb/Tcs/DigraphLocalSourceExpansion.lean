import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphLocalSourceSet

/-!
# digraph_local_source_expansion

Topic: graphs   Node: 780a0ae9ae34

Provenance: helper lemma. arXiv:2601.11847, Problem 5.2 and Proposition 2.3; a local-obstruction construction used in the OP-337 campaign.

The union of the out-neighborhood of v and the out-neighborhoods of the sources remaining after deletion of the closed out-neighborhood of v.
-/

def digraph_local_source_expansion {α : Type} [Fintype α] [DecidableEq α]
    (out : α → Finset α) (v : α) : Finset α :=
  out v ∪ Finset.univ.filter (fun w => ∃ u ∈ digraph_local_source_set out v, w ∈ out u)
