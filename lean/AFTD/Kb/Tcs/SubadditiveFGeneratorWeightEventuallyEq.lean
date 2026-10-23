import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFWeight
import AFTD.Kb.Tcs.SubadditiveFGenerator
import AFTD.Kb.Tcs.SubadditiveFGeneratorDeriv2

/-!
# subadditive_f_generator_weight_eventuallyEq

Topic: information   Node: 3e9736d4f09c

Provenance: helper lemma. helper for arXiv:2610.21231 (On the subadditivity of mutual f-information), Corollary 1 (x² f''(x) = g(x) = α x + s(x))

For s continuous on (0, ∞) and x > 0, the weight g(y) = y² f''(y) of the generator f of equation (4) agrees with α y + s(y) on a neighbourhood of x.
-/

theorem subadditive_f_generator_weight_eventuallyEq (α : ℝ) (s : ℝ → ℝ)
    (hs : ContinuousOn s (Set.Ioi 0)) {x : ℝ} (hx : 0 < x) :
    subadditive_f_weight (subadditive_f_generator α s) =ᶠ[nhds x] fun y => α * y + s y := by
  filter_upwards [lt_mem_nhds hx] with y hy
  unfold subadditive_f_weight
  rw [(subadditive_f_generator_deriv2 α s hs hy).deriv]
  field_simp
