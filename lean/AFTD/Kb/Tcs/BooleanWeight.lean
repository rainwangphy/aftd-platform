import AFTD.Prelude

/-!
# boolean_weight

Topic: quantum   Node: 07a8898dfc1f

Provenance: formalization of a published result. Source: arXiv:2610.09341, Section 4.1

The Hamming weight of a Boolean function on (Fin s → ZMod 2) is the number of points at which it evaluates to 1.
-/

open scoped Classical in
/-- The Hamming weight of a Boolean function c : (Fin s → ZMod 2) → ZMod 2. -/
noncomputable def boolean_weight {s : ℕ} (c : (Fin s → ZMod 2) → ZMod 2) : ℕ := (Finset.univ.filter (fun β => c β = 1)).card
