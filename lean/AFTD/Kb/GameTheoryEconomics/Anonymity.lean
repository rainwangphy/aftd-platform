import AFTD.Prelude

/-!
# Anonymity

Topic: social_choice   Node: 406966f76984

Provenance: formalization of a published result. Source: scout/2611-18282-safe-manipulation-of-tops-only-voting-rules.md:352

For a voting rule f : (Fin n → X) → X on n voters, f satisfies anonymity if for every profile t : Fin n → X and every permutation σ : Equiv.Perm (Fin n), f (t ∘ σ) = f t.
-/

/-- Anonymity for tops-only voting rules on Fin n. -/
def Anonymity {n : ℕ} {X : Type*} (f : (Fin n → X) → X) : Prop := ∀ (t : Fin n → X) (σ : Equiv.Perm (Fin n)), f (t ∘ σ) = f t
