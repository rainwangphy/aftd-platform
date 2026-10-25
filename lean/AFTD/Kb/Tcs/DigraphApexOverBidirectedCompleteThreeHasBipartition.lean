import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphApexOverBidirectedComplete
import AFTD.Kb.Tcs.DigraphCutCount

/-!
# digraph_apex_over_bidirected_complete_three_has_bipartition

Topic: graphs   Node: 6cac34f74184

Provenance: formalization of a published result. Source: arXiv:2610.21381 Conjecture 6.1

There exists a vertex bipartition V = A ⊔ B of the apex digraph D₃ on 5 vertices such that both directed cut counts e(A, B) and e(B, A) are at least 4, attaining the bound ⌈(3 - 1) * 16 / (2 * (2 * 3 - 1))⌉ = 4 of Conjecture 6.1 of arXiv:2610.21381.
-/

/-- For the extremal digraph D₃ on 5 vertices with 16 edges and minimum outdegree 3, there exists a vertex bipartition with both directed cuts at least 4, attaining the bound of Conjecture 6.1 with equality. -/
theorem digraph_apex_over_bidirected_complete_three_has_bipartition
    [DecidableRel (digraph_apex_over_bidirected_complete 3).Adj] :
    ∃ A B : Finset (Fin 5), Disjoint A B ∧ A ∪ B = Finset.univ ∧
      4 ≤ digraph_cut_count (digraph_apex_over_bidirected_complete 3) A B ∧
      4 ≤ digraph_cut_count (digraph_apex_over_bidirected_complete 3) B A := by
  have e : ‹DecidableRel (digraph_apex_over_bidirected_complete 3).Adj› =
      fun u v => (inferInstance : Decidable (u ≠ v ∧ v ≠ Fin.last 4)) := Subsingleton.elim _ _
  subst e
  refine ⟨{0, 1}, {2, 3, 4}, ?_⟩
  unfold digraph_cut_count
  decide
