import AFTD.Prelude
import AFTD.Kb.Optimization.PartialAssignmentLe
import AFTD.Kb.Optimization.IsMstCertificate
import AFTD.Kb.Optimization.IsMstFor

/-!
# mst_certificate_monotone

Topic: submodular   Node: 11858a3d2f99

Provenance: helper lemma. scout/2610-40844-stochastic-minimum-spanning-tree-identification-with-binary.md:262

If a partial realization β is an MST identification certificate for G (is_mst_certificate G β), and β is extended by γ (partial_assignment_le β γ), then γ is also an MST identification certificate for G (is_mst_certificate G γ).
-/

open scoped Classical in
/-- Extending an MST identification certificate yields another certificate. -/
theorem mst_certificate_monotone {V : Type*} [Fintype V] (G : SimpleGraph V)
    (β γ : G.edgeSet → Option Bool) (hcert : is_mst_certificate G β)
    (hle : partial_assignment_le β γ) : is_mst_certificate G γ := by
  rcases hcert with ⟨T, hTG, hT_tree, hT_mst⟩
  refine ⟨T, hTG, hT_tree, fun α hα => hT_mst α fun e b hb => hα e b (hle e b hb)⟩
