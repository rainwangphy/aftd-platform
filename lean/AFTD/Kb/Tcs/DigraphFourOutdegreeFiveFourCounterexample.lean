import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphLocalSourceSet
import AFTD.Kb.Tcs.DigraphLocalSourceExpansion
import AFTD.Kb.Tcs.DigraphLocalFourWitness

/-!
# digraph_four_outdegree_five_four_counterexample

Topic: graphs   Node: 0c72aa19d7ba

Provenance: original. Related work: arXiv:2601.11847, Problem 5.2 and Proposition 2.3; a local-obstruction construction used in the OP-337 campaign.

There exists a loopless source-free oriented digraph on 24 vertices with maximum outdegree at most four such that for every vertex v, if S(v) is the set of sources after deleting the closed out-neighborhood of v and E(v) is the union of the out-neighborhood of v with the out-neighborhood of S(v), then |E(v)| = |S(v)| and 5|E(v)| ≤ 4(|S(v)|+1). The graph also has an independent two-step out-dominating set of exactly six vertices.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem digraph_four_outdegree_five_four_counterexample :
    ∃ out : Fin 24 → Finset (Fin 24),
      (∀ v, v ∉ out v) ∧
      (∀ v, ∃ u, v ∈ out u) ∧
      (∀ u v, v ∈ out u → u ∉ out v) ∧
      (∀ v, (out v).card ≤ 4) ∧
      (∀ v, (digraph_local_source_expansion out v).card = (digraph_local_source_set out v).card ∧
        5 * (digraph_local_source_expansion out v).card ≤ 4 * ((digraph_local_source_set out v).card + 1)) ∧
      (∃ Q : Finset (Fin 24), Q.card = 6 ∧
        (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → v ∉ out u) ∧
        (∀ v, ∃ u ∈ Q, u = v ∨ v ∈ out u ∨ ∃ w, w ∈ out u ∧ v ∈ out w)) := by
  refine ⟨digraph_local_four_witness, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; fin_cases v <;> decide
  · intro v; fin_cases v <;> decide
  · intro u v; fin_cases u <;> fin_cases v <;> decide
  · intro v; fin_cases v <;> decide
  · intro v; fin_cases v <;> constructor <;> decide
  · refine ⟨{0,1,12,13,20,21}, by decide, ?_, ?_⟩
    · decide
    · intro v; fin_cases v <;> decide
