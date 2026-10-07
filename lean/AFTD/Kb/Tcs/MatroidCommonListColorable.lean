import AFTD.Prelude

/-!
# matroid_common_list_colorable

Topic: combinatorics   Node: de5a1f8929a7

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Sec. 1 (list coloring of a pair of matroids); lists of size at least k instead of exactly k, which is equivalent by shrinking lists

Two matroids M₁, M₂ on a common ground set E are k-list-colorable: for every assignment of finite color lists L(e) with |L(e)| ≥ k for all e ∈ E, there is an L-coloring, i.e. c(e) ∈ L(e) for all e and every color class independent in both matroids. (Colors are natural numbers, which loses nothing since only finitely many colors occur.)
-/

/-- `(M₁, M₂)` is `k`-list-colorable: for every assignment of finite lists of colors (natural numbers) with at least `k` colors to every element of the ground set, there is a choice of a color from each element's list such that every color class is independent in both matroids. -/
def matroid_common_list_colorable {α : Type*} (M₁ M₂ : Matroid α) (k : ℕ) : Prop :=
  ∀ L : α → Finset ℕ, (∀ e ∈ M₁.E, k ≤ (L e).card) →
    ∃ c : α → ℕ, (∀ e ∈ M₁.E, c e ∈ L e) ∧ ∀ γ : ℕ,
      M₁.Indep {e | e ∈ M₁.E ∧ c e = γ} ∧ M₂.Indep {e | e ∈ M₁.E ∧ c e = γ}
