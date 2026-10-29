import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsTwoLinked
import AFTD.Kb.Tcs.DigraphIsUnilaterallyTwoLinked
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_unilaterally_two_linked_of_two_linked

Topic: graphs   Node: b286f3349a58

Provenance: helper lemma. arXiv:2610.36895 Sec. 1

Every 2-linked digraph is unilaterally 2-linked.
-/

/-- Every 2-linked digraph is unilaterally 2-linked. -/
theorem digraph_unilaterally_two_linked_of_two_linked {V : Type*} (D : Digraph V)
    (h : digraph_is_two_linked D) : digraph_is_unilaterally_two_linked D := by
  intro s₁ t₁ s₂ t₂ hnd
  obtain ⟨p₁, p₂, hp₁, hp₂, hdisj⟩ := h s₁ t₁ s₂ t₂ hnd
  exact ⟨p₁, p₂, Or.inl hp₁, Or.inl hp₂, hdisj⟩
