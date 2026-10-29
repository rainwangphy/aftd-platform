import AFTD.Prelude
import AFTD.Kb.Tcs.IsConferenceGraph

/-!
# exists_conference_graph

Topic: combinatorics   Node: 46f1068c6c62

Provenance: formalization of a published result. Source: arXiv:2610.36522 Definition 6

exists_conference_graph v asserts the existence of a conference graph of order v on Fin v.
-/

/-- Existence of a conference graph on Fin v. -/
def exists_conference_graph (v : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin v)) (_ : DecidableRel G.Adj),
    is_conference_graph G
