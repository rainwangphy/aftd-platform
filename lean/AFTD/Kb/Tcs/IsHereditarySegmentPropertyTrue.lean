import AFTD.Prelude
import AFTD.Kb.Tcs.IsHereditarySegmentProperty

/-!
# isHereditarySegmentProperty_true

Topic: online_algorithms   Node: 769c6640cfb7

Provenance: helper lemma. arXiv:2610.23130, Section 1

The constantly true predicate on Finset (Sym2 (ℝ × ℝ)) is a hereditary segment property.
-/

/-- The trivial always-true property is a hereditary segment property. -/
theorem isHereditarySegmentProperty_true : IsHereditarySegmentProperty (fun _ => True) := by
  refine ⟨trivial, ?_⟩
  intro s t _ _
  trivial
