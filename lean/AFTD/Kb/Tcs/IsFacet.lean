import AFTD.Prelude

/-!
# is_facet

Topic: combinatorics   Node: adb45d07b740

Provenance: formalization of a published result. Source: folklore; Ziegler, Lectures on Polytopes

A subset F of a real vector space is a facet of P if F is a maximal proper nonempty extreme set of P.
-/

/-- A facet of a set P in a real vector space is a maximal proper nonempty extreme subset of P. -/
def is_facet {E : Type*} [AddCommMonoid E] [Module ℝ E] (P F : Set E) : Prop := IsExtreme ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧ ∀ G, IsExtreme ℝ P G → F ⊆ G → G = F ∨ G = P
