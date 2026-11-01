import AFTD.Prelude
import AFTD.Kb.Tcs.IsSignedDictator

/-!
# dictator_dist

Topic: information   Node: ed8c00321e63

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:977

The dictator distance delta(f) of a real-valued function f : (Fin n → Bool) → ℝ on the hypercube Fin n → Bool is the infimum over all signed dictators g : (Fin n → Bool) → ℝ satisfying is_signed_dictator n g of (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, if f x ≠ g x then 1 else 0.
-/

open scoped BigOperators in
/-- The distance of a Boolean function f to the nearest signed dictator under the uniform distribution. -/
noncomputable def dictator_dist (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ := ⨅ (g : (Fin n → Bool) → ℝ) (_ : is_signed_dictator n g),
    (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, if f x ≠ g x then 1 else 0
