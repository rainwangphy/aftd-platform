import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForced

/-!
# is_zero_forcing_set_mono

Topic: graphs   Node: 66e98957600d

Provenance: helper lemma. arXiv:2611.11352 Sec. 1

If S is a zero forcing set of a simple graph G and S is a subset of S', then S' is also a zero forcing set of G.
-/

private theorem zf_mono_inclusion_induction {V : Type*} (G : SimpleGraph V) {S T : Set V} (h : S ⊆ T) :
    ∀ v, ZeroForced G S v → ZeroForced G T v := by
  intro v hv
  induction hv with
  | init v hvS => exact ZeroForced.init v (h hvS)
  | step u w hu huw hothers ihu ihothers =>
    exact ZeroForced.step u w ihu huw ihothers

/-- Supersets of zero forcing sets are zero forcing sets. -/
theorem is_zero_forcing_set_mono {V : Type*} (G : SimpleGraph V) {S S' : Set V}
    (h : S ⊆ S') (hS : is_zero_forcing_set G S) : is_zero_forcing_set G S' := by
  intro v
  exact zf_mono_inclusion_induction G h v (hS v)
