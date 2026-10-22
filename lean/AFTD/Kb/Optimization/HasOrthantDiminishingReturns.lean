import AFTD.Prelude
import AFTD.Kb.Optimization.KSubmodLe

/-!
# has_orthant_diminishing_returns

Topic: submodular   Node: 9ac62b84ca0d

Provenance: formalization of a published result. Source: arXiv:2610.26677, Eq. (2)

A function f : (Fin n → Option (Fin k)) → ℝ has orthant diminishing returns if for all x ≤ y, unassigned e in y, and label i, f (y + i 1_e) - f y ≤ f (x + i 1_e) - f x.
-/

/-- Orthant diminishing returns (orthant submodularity) for a function on assignments. -/
def has_orthant_diminishing_returns {n k : ℕ} (f : (Fin n → Option (Fin k)) → ℝ) : Prop := ∀ (x y : Fin n → Option (Fin k)) (e : Fin n) (i : Fin k),
    k_submod_le x y → y e = none →
      f (Function.update y e (some i)) - f y ≤ f (Function.update x e (some i)) - f x
