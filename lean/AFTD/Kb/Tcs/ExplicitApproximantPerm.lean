import AFTD.Prelude
import AFTD.Kb.Tcs.ExplicitApproximant
import AFTD.Kb.Tcs.Bit
import AFTD.Kb.Tcs.TopCoefficient
import AFTD.Kb.Tcs.FullMonomial
import AFTD.Kb.Tcs.ParityCharacter

/-!
# explicitApproximant_perm

Topic: circuits   Node: ea946d6a87db

Provenance: formalization of a published result. Source: arXiv:2610.19174, Listing A.15

For any Boolean function f : (Fin n → Bool) → Bool on n variables, any permutation e : Equiv.Perm (Fin n), if f (x ∘ e) = f x for all x then explicitApproximant f (x ∘ e) = explicitApproximant f x for all x.
-/

/-- Symmetry of f under coordinate permutations implies symmetry of P_f. -/
theorem explicitApproximant_perm {n : ℕ} (f : (Fin n → Bool) → Bool)
    (e : Equiv.Perm (Fin n)) (hf : ∀ x, f (x ∘ e) = f x) (x : Fin n → Bool) :
    explicitApproximant f (x ∘ e) = explicitApproximant f x := by
  -- `topCoefficient f` does not depend on the input `x`, so the only inputs that
  -- move are `f`, `fullMonomial` and `parityCharacter`.
  have hmul : fullMonomial (x ∘ e) = fullMonomial x := by
    simp only [fullMonomial]
    exact Equiv.prod_comp e (fun i => bit (x i))
  have hpar : parityCharacter (x ∘ e) = parityCharacter x := by
    simp only [parityCharacter]
    exact Equiv.prod_comp e (fun i => if x i = true then (1 : ℝ) else -1)
  simp only [explicitApproximant, hf x, hmul, hpar]
