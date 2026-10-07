import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_chromatic_number

Topic: combinatorics   Node: 0bb5369a358b

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Sec. 1

The common list chromatic number χ_ℓ(M₁, M₂): the least k such that (M₁, M₂) is k-list-colorable.
-/

/-- The common list chromatic number `χ_ℓ(M₁, M₂)`: the least `k` such that `(M₁, M₂)` is `k`-list-colorable (`0` if there is none). -/
noncomputable def matroid_common_list_chromatic_number {α : Type*} (M₁ M₂ : Matroid α) : ℕ :=
  sInf {k | matroid_common_list_colorable M₁ M₂ k}
