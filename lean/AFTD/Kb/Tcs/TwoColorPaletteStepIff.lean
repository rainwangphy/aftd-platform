import AFTD.Prelude

/-!
# two_color_palette_step_iff

Topic: graphs   Node: 420e215dd893

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

For two distinct colors x and y in a two-element palette, y differs from z exactly when membership of z in the palette forces z=x.
-/

theorem two_color_palette_step_iff
    {Ω : Type*} [DecidableEq Ω] (P : Finset Ω) (x y z : Ω)
    (hcard : P.card = 2) (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) :
    y ≠ z ↔ (z ∈ P → z = x) := by
  have hsub : ({x, y} : Finset Ω) ⊆ P := by
    simp [Finset.insert_subset, hx, hy]
  have hsize : P.card ≤ ({x, y} : Finset Ω).card := by
    simp [hcard, hxy]
  have hpair : ({x, y} : Finset Ω) = P := Finset.eq_of_subset_of_card_le hsub hsize
  constructor
  · intro h hz
    have hz' : z = x ∨ z = y := by simpa [← hpair] using hz
    exact hz'.resolve_right (Ne.symm h)
  · intro h heq
    subst z
    exact hxy (h hy).symm
