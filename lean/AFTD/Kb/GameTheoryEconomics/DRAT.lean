import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsKnownVoterSafelyManipulable

/-!
# d_RAT

Topic: social_choice   Node: 85276b94e67d

Provenance: formalization of a published result. Source: scout/2611-18282-safe-manipulation-of-tops-only-voting-rules.md:276

The RAT-degree d_RAT f of a tops-only voting rule f : (Fin n → X) → X is the minimum natural number k < n such that IsKnownVoterSafelyManipulable f k holds, or n if no such k exists.
-/

/-- The RAT-degree of a tops-only voting rule on Fin n. -/
noncomputable def d_RAT {n : ℕ} {X : Type*} (f : (Fin n → X) → X) : ℕ := open Classical in if h : ∃ k, k < n ∧ IsKnownVoterSafelyManipulable f k then Nat.find h else n
