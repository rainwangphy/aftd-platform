import AFTD.Prelude

/-!
# matroid_common_colorable

Topic: combinatorics   Node: 4e95036da340

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Sec. 1 (coloring of a pair of matroids)

Two matroids M₁, M₂ on a common ground set E have a common coloring with k colors: a map c : E → {0, …, k−1} each of whose color classes is independent in both M₁ and M₂.
-/

/-- `(M₁, M₂)` has a common coloring with `k` colors: a map `c` giving each element of the ground set of `M₁` a color in `{0, …, k - 1}` such that every color class is independent in both matroids. -/
def matroid_common_colorable {α : Type*} (M₁ M₂ : Matroid α) (k : ℕ) : Prop :=
  ∃ c : α → ℕ, (∀ e ∈ M₁.E, c e < k) ∧ ∀ γ : ℕ,
    M₁.Indep {e | e ∈ M₁.E ∧ c e = γ} ∧ M₂.Indep {e | e ∈ M₁.E ∧ c e = γ}
