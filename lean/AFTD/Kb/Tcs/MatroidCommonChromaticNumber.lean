import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonColorable

/-!
# matroid_common_chromatic_number

Topic: combinatorics   Node: 525e20610607

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Sec. 1

The common chromatic number χ(M₁, M₂): the least k such that (M₁, M₂) has a common coloring with k colors.
-/

/-- The common chromatic number `χ(M₁, M₂)`: the least number of colors in a common coloring (`0` if there is none). -/
noncomputable def matroid_common_chromatic_number {α : Type*} (M₁ M₂ : Matroid α) : ℕ :=
  sInf {k | matroid_common_colorable M₁ M₂ k}
