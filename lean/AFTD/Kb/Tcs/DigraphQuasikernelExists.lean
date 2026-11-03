import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphQuasikernelOnSubset

/-!
# digraph_quasikernel_exists

Topic: graphs   Node: 5cf369ef5fde

Provenance: helper lemma. Standard qualitative quasi-kernel existence construction, recalled in arXiv:2601.11847 Section 1.1; foundational helper for OP-337.

Every finite digraph contains an independent set from which every vertex is reachable in at most two directed arcs.
-/

theorem digraph_quasikernel_exists
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] :
    ∃ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) := by
  obtain ⟨Q,_,hind,hcover⟩ := digraph_quasikernel_on_subset D Finset.univ
  refine ⟨Q,hind,?_⟩
  intro v
  obtain ⟨u,hu,h⟩ := hcover v (Finset.mem_univ v)
  refine ⟨u,hu,?_⟩
  rcases h with heq | hadj | ⟨w,_,huw,hwv⟩
  · exact Or.inl heq
  · exact Or.inr (Or.inl hadj)
  · exact Or.inr (Or.inr ⟨w,huw,hwv⟩)
