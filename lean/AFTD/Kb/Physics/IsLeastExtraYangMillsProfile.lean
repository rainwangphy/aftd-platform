import AFTD.Prelude
import AFTD.Kb.Physics.YangMillsAMinus
import AFTD.Kb.Physics.IsYangMillsSmoothProfile

/-!
# is_least_extra_yang_mills_profile

Topic: classical_fields   Node: e6d517faeef1

Provenance: formalization of a published result. Source: arXiv:2610.36784

For a natural number dimension d : ℕ and a function u : ℝ → ℝ, is_least_extra_yang_mills_profile d u asserts that there exists a real shooting parameter a > yang_mills_a_minus (d : ℝ) such that is_yang_mills_smooth_profile d u a holds, and for every function v : ℝ → ℝ and real parameter a' > yang_mills_a_minus (d : ℝ), if is_yang_mills_smooth_profile d v a' holds then a ≤ a'.
-/

/-- Predicate that u is an extra smooth profile beyond the explicit minus branch with the least shooting parameter a > a_-(d). -/
def is_least_extra_yang_mills_profile (d : ℕ) (u : ℝ → ℝ) : Prop := ∃ a : ℝ, a > yang_mills_a_minus (d : ℝ) ∧
    is_yang_mills_smooth_profile d u a ∧
    ∀ (v : ℝ → ℝ) (a' : ℝ), a' > yang_mills_a_minus (d : ℝ) →
      is_yang_mills_smooth_profile d v a' → a ≤ a'
