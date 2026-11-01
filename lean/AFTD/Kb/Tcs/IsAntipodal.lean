import AFTD.Prelude

/-!
# is_antipodal

Topic: information   Node: 08f7780f5ee8

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:147

A function f from the Boolean hypercube {0,1}^n to the reals is an antipodal Boolean function if it takes values in {-1, 1} and reverses sign under the global bit flip: f(not x) = -f(x) for all x.
-/

/-- Predicate that a function on {0,1}^n is an antipodal Boolean function taking values in {-1, 1}. -/
def is_antipodal (n : ℕ) (f : (Fin n → Bool) → ℝ) : Prop := (∀ x, f x = 1 ∨ f x = -1) ∧ ∀ x, f (fun i ↦ !x i) = -f x
