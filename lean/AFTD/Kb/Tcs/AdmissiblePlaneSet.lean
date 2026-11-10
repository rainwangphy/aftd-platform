import AFTD.Prelude
import AFTD.Kb.Tcs.AffinePlane

/-!
# admissible_plane_set

Topic: combinatorics   Node: da5c6b6d5810

Provenance: formalization of a published result. Source: arXiv:2611.12153 Section 1

Let p be a prime. A subset S of (ZMod p)^3 is an admissible plane set if its cardinality is p^2 and for every nonzero linear functional f on (ZMod p)^3 and scalar c in ZMod p, the cardinality of S ∩ affine_plane f c is divisible by p.
-/

/-- A set S in (ZMod p)^3 is an admissible plane set if it has p^2 points and every affine plane meets S in a multiple of p points. -/
def admissible_plane_set (p : ℕ) [Fact p.Prime] (S : Set (Fin 3 → ZMod p)) : Prop := S.ncard = p ^ 2 ∧
  ∀ (f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p) (_ : f ≠ 0) (c : ZMod p),
    p ∣ (S ∩ affine_plane f c).ncard
