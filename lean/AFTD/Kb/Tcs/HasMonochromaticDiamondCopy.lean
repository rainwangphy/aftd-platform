import AFTD.Prelude

/-!
# has_monochromatic_diamond_copy

Topic: combinatorics   Node: f99984a4b586

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

For a colouring χ of the subsets of Fin d with k colours, has_monochromatic_diamond_copy j d col χ holds if there are sets bot ⊂ top of colour col and j sets mid i, strictly between bot and top, pairwise incomparable, all of colour col — i.e. a monochromatic induced copy of the j-diamond D_j (bottom, j incomparable middles, top) in the colouring χ.
-/

/-- A monochromatic induced copy of the j-diamond, stated directly as bot ⊂ j pairwise incomparable middles ⊂ top, all of one colour. -/
def has_monochromatic_diamond_copy (j d : ℕ) {k : ℕ} (col : Fin k) (χ : Finset (Fin d) → Fin k) : Prop := ∃ bot top : Finset (Fin d), bot ⊂ top ∧ χ bot = col ∧ χ top = col ∧
    ∃ mid : Fin j → Finset (Fin d),
      (∀ i, bot ⊂ mid i ∧ mid i ⊂ top ∧ χ (mid i) = col) ∧
      (∀ i i', i ≠ i' → ¬ mid i ⊆ mid i')
