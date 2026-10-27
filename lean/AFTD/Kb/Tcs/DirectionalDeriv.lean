import AFTD.Prelude

/-!
# directional_deriv

Topic: cryptography   Node: 0199378a83fc

Provenance: formalization of a published result. Source: arXiv:2610.32239 Section 2

The directional derivative of a Boolean function g on (Fin n → ZMod 2) along direction v is defined by D_v g(x) = g(x + v) + g(x).
-/

/-- Directional derivative of a Boolean function along a direction vector. -/
def directional_deriv {n : ℕ} (v : Fin n → ZMod 2) (g : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 := fun x => g (x + v) + g x
