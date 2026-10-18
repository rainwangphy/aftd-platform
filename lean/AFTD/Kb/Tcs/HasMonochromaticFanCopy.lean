import AFTD.Prelude

/-!
# has_monochromatic_fan_copy

Topic: combinatorics   Node: 36cabce87cf1

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

For a colouring χ of the subsets of Fin d with k colours, has_monochromatic_fan_copy j d col χ holds if there is a set top of colour col with j pairwise incomparable subsets mid i of top, all of colour col — i.e. a monochromatic induced copy of the poset F_j consisting of a maximum element over an antichain of size j (the j-diamond with its bottom element deleted).
-/

/-- A monochromatic induced copy of F_j (a top element over an antichain of size j), stated directly in terms of sets. -/
def has_monochromatic_fan_copy (j d : ℕ) {k : ℕ} (col : Fin k) (χ : Finset (Fin d) → Fin k) : Prop := ∃ top : Finset (Fin d), χ top = col ∧
    ∃ mid : Fin j → Finset (Fin d),
      (∀ i, mid i ⊂ top ∧ χ (mid i) = col) ∧
      (∀ i i', i ≠ i' → ¬ mid i ⊆ mid i')
