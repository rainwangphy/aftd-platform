import AFTD.Prelude

/-!
# boolean_derivative

Topic: cryptography   Node: efbd1f7ea796

Provenance: formalization of a published result. Source: arXiv:2610.32239, Section 2

The directional derivative of a Boolean function f on (Fin n → ZMod 2) along a vector v is the function x ↦ f(x) + f(x + v).
-/

/-- Directional derivative of a Boolean function along a direction vector. -/
def boolean_derivative {n : ℕ} (v : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 := fun x => f x + f (x + v)
