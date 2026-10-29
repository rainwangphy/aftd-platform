import AFTD.Prelude

/-!
# boolean_derivative_signing_flat

Topic: cryptography   Node: d476dcc24ac9

Provenance: helper lemma. step towards boolean_derivative_bent_partner_exists

A pair of Boolean functions (h, a) on (Fin 7 → ZMod 2) is a flat signing if, on each of the two level sets {u | h u = s}, the signed Walsh sums Σ_{u, h u = s} (-1)^(a u + w·u) have absolute value 8 for every frequency w.
-/

/-- Flat signing: both level-set signed Walsh sums of a 7-variable Boolean function have absolute value 8; exactly the condition that the lift (u,y) ↦ a u + y·h u is bent on 8 variables. -/
def boolean_derivative_signing_flat (h a : (Fin 7 → ZMod 2) → ZMod 2) : Prop := ∀ s : ZMod 2, ∀ w : Fin 7 → ZMod 2,
    |∑ u : Fin 7 → ZMod 2, if h u = s then (if a u + ∑ i, u i * w i = 0 then (1:ℤ) else -1) else 0| = 8
