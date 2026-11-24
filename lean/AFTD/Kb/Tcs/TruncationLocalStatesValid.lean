import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff

/-!
# truncation_local_states_valid

Topic: graphs   Node: 80b6bf0148f5

Provenance: helper lemma. step towards two_odd_factor_cycles_except_five_via_off_palette_defect

The four local-state conditions of Lemma 2.1 of arXiv:2610.41950, bundled: at every vertex the external colours c v are injective on the incident edges, the hidden colours h v are injective on them, every hidden colour differs from every external colour at the vertex, and along every edge the two ends agree on the external colour and their exposed pairs are disjoint.
-/

/-- The bundled local-state hypotheses of `truncation_local_states_strong_coloring_iff`. -/
def truncation_local_states_valid {V E Ω : Type*} (ends : E → Sym2 V) (c h : V → E → Ω) : Prop :=
  (∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f) ∧
    (∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f) ∧
    (∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f) ∧
    (∀ e u v, ends e = s(u, v) →
      c u e = c v e ∧ Disjoint (truncation_exposed_pair ends c h u e)
        (truncation_exposed_pair ends c h v e))
