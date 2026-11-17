import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PreferenceWithUniqueTop
import AFTD.Kb.GameTheoryEconomics.IsSafeManipulation

/-!
# IsKnownVoterSafelyManipulable

Topic: social_choice   Node: 96e3b51441b5

Provenance: formalization of a published result. Source: scout/2611-18282-safe-manipulation-of-tops-only-voting-rules.md:260

For a tops-only voting rule f : (Fin n → X) → X and k : ℕ, f is k-known-voter safely manipulable if there exist a voter i : Fin n, a subset K : Finset (Fin n) with i ∉ K and K.card = k, reports t_K : Fin n → X, a preference R : PreferenceWithUniqueTop X, and a misreported alternative s_i : X such that IsSafeManipulation f i K t_K R s_i holds.
-/

/-- k-known-voter safely manipulable for tops-only voting rules on Fin n. -/
def IsKnownVoterSafelyManipulable {n : ℕ} {X : Type*} (f : (Fin n → X) → X) (k : ℕ) : Prop := ∃ (i : Fin n) (K : Finset (Fin n)), i ∉ K ∧ K.card = k ∧ ∃ (t_K : Fin n → X) (R : PreferenceWithUniqueTop X) (s_i : X), IsSafeManipulation f i K t_K R s_i
