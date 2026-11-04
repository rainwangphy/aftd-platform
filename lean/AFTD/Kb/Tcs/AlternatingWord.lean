import AFTD.Prelude

/-!
# alternating_word

Topic: information   Node: 1ec59f25a04d

Provenance: formalization of a published result. Source: arXiv:2611.01064, Section 2

Given a natural number n and a boolean start, alternating_word n start is the function from Fin n to Bool that maps each index i : Fin n to start if i.val % 2 = 0, and to !start otherwise.
-/

/-- The alternating binary word of length n starting with a given bit. -/
def alternating_word (n : ℕ) (start : Bool) : Fin n → Bool := fun i => if i.val % 2 = 0 then start else !start
