import AFTD.Prelude

/-!
# is_ternary_line_cover

Topic: combinatorics   Node: 452ddb7c18f0

Provenance: formalization of a published result. Source: arXiv:2610.32789, Section 3.1

Given an explicit natural number n, a finite set B : Finset (Fin n → ZMod 3) is a ternary line cover if for every coordinate i : Fin n and every vector c : Fin n → ZMod 3, there exists an element t : ZMod 3 such that Function.update c i t belongs to B.
-/

/-- A finite set of (Fin n → ZMod 3) meets every axis-parallel coordinate line. -/
def is_ternary_line_cover (n : ℕ) (B : Finset (Fin n → ZMod 3)) : Prop := ∀ (i : Fin n) (c : Fin n → ZMod 3), ∃ t : ZMod 3, Function.update c i t ∈ B
