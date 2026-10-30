import AFTD.Prelude
import AFTD.Kb.Tcs.IsTernaryLineCover

/-!
# is_minimal_ternary_line_cover

Topic: combinatorics   Node: 149cc12dab06

Provenance: formalization of a published result. Source: arXiv:2610.32789, Section 3.1

Given an explicit natural number n, a finite set B : Finset (Fin n → ZMod 3) is an inclusion-minimal ternary line cover if B is a ternary line cover and every sub-finset B' ⊆ B that is also a ternary line cover equals B.
-/

/-- A ternary line cover is inclusion-minimal if no proper sub-finset is a line cover. -/
def is_minimal_ternary_line_cover (n : ℕ) (B : Finset (Fin n → ZMod 3)) : Prop := is_ternary_line_cover n B ∧ ∀ B' ⊆ B, is_ternary_line_cover n B' → B' = B
