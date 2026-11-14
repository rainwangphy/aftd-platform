import AFTD.Prelude
import AFTD.Kb.Tcs.RevComp

/-!
# rc_substring_free

Topic: approximation   Node: 1e492d591842

Provenance: formalization of a published result. Source: arXiv:2611.16573, Section 2

For a complement map cm : Γ → Γ and a finite set S : Finset (List Γ), rc_substring_free cm S holds when for all x, y ∈ S with x ≠ y, x is not an infix (contiguous sublist) of y and x is not an infix of rev_comp cm y; nothing is required when x = y.
-/

/-- A set of strings is RC-substring-free: no string is a substring of another one or of its reverse complement. -/
def rc_substring_free {Γ : Type*} (cm : Γ → Γ) (S : Finset (List Γ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ x <:+: y ∧ ¬ x <:+: rev_comp cm y
