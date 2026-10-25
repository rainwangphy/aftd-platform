import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphApexOverBidirectedComplete
import AFTD.Kb.Tcs.DigraphCutCount

/-!
# digraph_apex_over_bidirected_complete_two_has_bipartition

Topic: graphs   Node: 5f6c57137844

Provenance: formalization of a published result. Source: arXiv:2610.21381 Conjecture 6.1

There exists a vertex bipartition V = A ⊔ B of the apex digraph D₂ on 4 vertices such that both directed cut counts e(A, B) and e(B, A) are at least 2, satisfying the bound ⌈(2 - 1) * 9 / (2 * (2 * 2 - 1))⌉ = 2 of Conjecture 6.1 of arXiv:2610.21381.
-/

instance digraph_apex_over_bidirected_complete_two_has_bipartition_decidableRel :
    DecidableRel (digraph_apex_over_bidirected_complete 2).Adj := by
  dsimp [digraph_apex_over_bidirected_complete]
  infer_instance

/-- For the digraph D₂ on 4 vertices with 9 edges and minimum outdegree 2, there exists a vertex bipartition with both directed cuts at least 2, matching the bound of Conjecture 6.1. -/
theorem digraph_apex_over_bidirected_complete_two_has_bipartition
    [DecidableRel (digraph_apex_over_bidirected_complete 2).Adj] :
    ∃ A B : Finset (Fin 4), Disjoint A B ∧ A ∪ B = Finset.univ ∧
      2 ≤ digraph_cut_count (digraph_apex_over_bidirected_complete 2) A B ∧
      2 ≤ digraph_cut_count (digraph_apex_over_bidirected_complete 2) B A := by
  have := Subsingleton.elim ‹DecidableRel (digraph_apex_over_bidirected_complete 2).Adj›
    digraph_apex_over_bidirected_complete_two_has_bipartition_decidableRel
  subst this
  refine ⟨{0}, {1, 2, 3}, ?_⟩
  decide
