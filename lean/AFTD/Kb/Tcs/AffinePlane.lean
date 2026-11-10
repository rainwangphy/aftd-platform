import AFTD.Prelude

/-!
# affine_plane

Topic: combinatorics   Node: e03ba0c9f02b

Provenance: formalization of a published result. Source: arXiv:2611.12153 Section 1

For a natural number p, the affine plane defined by a linear functional f on (ZMod p)^3 and scalar c in ZMod p is the fiber {x | f x = c}.
-/

/-- The affine plane defined by a linear functional f and scalar c in (ZMod p)^3. -/
def affine_plane {p : ℕ} (f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p) (c : ZMod p) : Set (Fin 3 → ZMod p) := {x | f x = c}
