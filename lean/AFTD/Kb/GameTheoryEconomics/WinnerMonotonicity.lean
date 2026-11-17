import AFTD.Prelude

/-!
# WinnerMonotonicity

Topic: social_choice   Node: b4054a21268e

Provenance: formalization of a published result. Source: scout/2611-18282-safe-manipulation-of-tops-only-voting-rules.md:339

For a voting rule f : (Fin n → X) → X on n voters, f satisfies winner monotonicity if for every profile t : Fin n → X, voter i : Fin n, and alternative x : X, f t = x implies f (Function.update t i x) = x.
-/

/-- Winner monotonicity for tops-only voting rules on Fin n. -/
def WinnerMonotonicity {n : ℕ} {X : Type*} (f : (Fin n → X) → X) : Prop := ∀ (t : Fin n → X) (i : Fin n) (x : X), f t = x → f (Function.update t i x) = x
