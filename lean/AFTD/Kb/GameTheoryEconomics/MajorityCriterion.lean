import AFTD.Prelude

/-!
# MajorityCriterion

Topic: social_choice   Node: 7e77da5e5294

Provenance: formalization of a published result. Source: scout/2611-18282-safe-manipulation-of-tops-only-voting-rules.md:646

A tops-only voting rule f satisfies the majority criterion if whenever strictly more than n / 2 voters report x as their top, f selects x.
-/

/-- Majority criterion: an alternative reported by a strict majority of voters must win. -/
def MajorityCriterion {n : ℕ} {X : Type*} (f : (Fin n → X) → X) : Prop := open Classical in ∀ (t : Fin n → X) (x : X), n / 2 < Finset.card {i : Fin n | t i = x} → f t = x
