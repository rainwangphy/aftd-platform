import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PreferenceWithUniqueTop

/-!
# IsSafeManipulation

Topic: social_choice   Node: 8dd3c5af64cb

Provenance: formalization of a published result. Source: scout/2611-18282-safe-manipulation-of-tops-only-voting-rules.md:242

For a tops-only voting rule f : (Fin n → X) → X, a misreport s_i : X is a safe manipulation for voter i : Fin n given known reports t_K : Fin n → X on a subset K : Finset (Fin n) and true preference R : PreferenceWithUniqueTop X with sincere top R.top if there exists a completion profile t : Fin n → X agreeing with t_K on K and with t i = R.top such that ¬ R.rel (f t) (f (Function.update t i s_i)), and for every completion profile t : Fin n → X agreeing with t_K on K and with t i = R.top, R.rel (f (Function.update t i s_i)) (f t).
-/

/-- Safe manipulation for tops-only voting rules on Fin n. -/
def IsSafeManipulation {n : ℕ} {X : Type*} (f : (Fin n → X) → X) (i : Fin n) (K : Finset (Fin n)) (t_K : Fin n → X) (R : PreferenceWithUniqueTop X) (s_i : X) : Prop := (∃ t : Fin n → X, t i = R.top ∧ (∀ j ∈ K, t j = t_K j) ∧ ¬ R.rel (f t) (f (Function.update t i s_i))) ∧ (∀ t : Fin n → X, t i = R.top → (∀ j ∈ K, t j = t_K j) → R.rel (f (Function.update t i s_i)) (f t))
