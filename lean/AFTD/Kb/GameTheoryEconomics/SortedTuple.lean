import AFTD.Prelude

/-!
# sorted_tuple

Topic: fair_division   Node: ccce8b51f504

Provenance: formalization of a published result. Source: Mathlib/Data/Fin/Tuple/Sort.lean

For any tuple u : Fin m → ℝ, its sorted tuple is u ∘ Tuple.sort u, which reorders the values of u in nondecreasing order.
-/

/-- The sorted tuple of u : Fin m -> Real in nondecreasing order obtained by composing with Tuple.sort u. -/
noncomputable def sorted_tuple {m : ℕ} (u : Fin m → ℝ) : Fin m → ℝ := u ∘ Tuple.sort u
