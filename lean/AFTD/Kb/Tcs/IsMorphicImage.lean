import AFTD.Prelude

/-!
# is_morphic_image

Topic: combinatorics   Node: d89b3b5789f9

Provenance: formalization of a published result. Source: arXiv:2611.13676

An infinite word z is the morphic image of an infinite word w under f : α → List β if for every n, applying f to the prefix of length n of w yields the prefix of z of that length.
-/

/-- An infinite word z is the morphic image of an infinite word w under a morphism f if every prefix of w maps under f to the corresponding prefix of z. -/
def is_morphic_image {α β : Type*} (z : ℕ → β) (f : α → List β) (w : ℕ → α) : Prop := ∀ n : ℕ, ((List.range n).map w).flatMap f = (List.range (((List.range n).map w).flatMap f).length).map z
