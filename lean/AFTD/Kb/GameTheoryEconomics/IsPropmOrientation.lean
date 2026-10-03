import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.OrientationMaximinValue
import AFTD.Kb.GameTheoryEconomics.OrientationPropShare

/-!
# is_propm_orientation

Topic: fair_division   Node: 68da4b9eb531

An orientation is PROPm if every agent's value for her bundle plus her PROPm slack d_i is at least her proportional share.
-/

/-- The orientation `σ` is PROPm: every agent `i` has `v_i(π_i) + d_i ≥ PROP_i`. -/
def is_propm_orientation {m n : ℕ} (ends : Fin m → Fin n × Fin n)
    (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i, orientation_prop_share ends u i ≤
    additive_valuation (u i) (bundle_of σ i) + orientation_maximin_value ends u σ i
