import AFTD.Prelude

/-!
# is_coverable

Topic: combinatorics   Node: 82944cd1fe38

Provenance: formalization of a published result. Source: arXiv:2611.13535, Definition 2.1

A subset S of the complex plane is coverable by non-overlapping closed unit disks if there exists a set C of disk centers such that ||c - c'|| >= 2 for all distinct c, c' in C, and for every point x in S there exists c in C such that ||x - c|| <= 1.
-/

/-- A set in the complex plane is coverable by non-overlapping closed unit disks. -/
def is_coverable (S : Set ℂ) : Prop := ∃ C : Set ℂ, (∀ ⦃c c' : ℂ⦄, c ∈ C → c' ∈ C → c ≠ c' → 2 ≤ ‖c - c'‖) ∧ ∀ x ∈ S, ∃ c ∈ C, ‖x - c‖ ≤ 1
