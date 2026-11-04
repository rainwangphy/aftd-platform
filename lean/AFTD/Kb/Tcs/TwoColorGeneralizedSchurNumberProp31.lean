import AFTD.Prelude
import AFTD.Kb.Tcs.SchurTwoUpperBound
import AFTD.Kb.Tcs.SchurTwoLowerBound

/-!
# two_color_generalized_schur_number_prop31

Topic: combinatorics   Node: fc1b39d28c30

Provenance: formalization of a published result. Source: arXiv:2611.01714 Proposition 3.1

For every integer k ≥ 3, every 2-coloring of Fin (k^2 + k - 1) admits a monochromatic solution to (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1, and the 2-coloring of Fin (k^2 + k - 2) defined by color 0 on [1, k-1] ∪ [k^2, k^2+k-2] and color 1 on [k, k^2-1] contains no monochromatic solution.
-/

/-- Proposition 3.1: Two-color generalized Schur number T_k(2) = k^2 + k - 1 for x + (k - 1)y = z. -/
theorem two_color_generalized_schur_number_prop31 (k : ℕ) (hk : 3 ≤ k) :
    (∀ c : Fin (k^2 + k - 1) → Fin 2,
      ∃ x y z : Fin (k^2 + k - 1), c x = c y ∧ c y = c z ∧
        (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1) ∧
    ¬ ∃ x y z : Fin (k^2 + k - 2),
      (if x.val + 1 ≤ k - 1 ∨ k^2 ≤ x.val + 1 then (0 : Fin 2) else 1) =
        (if y.val + 1 ≤ k - 1 ∨ k^2 ≤ y.val + 1 then (0 : Fin 2) else 1) ∧
      (if y.val + 1 ≤ k - 1 ∨ k^2 ≤ y.val + 1 then (0 : Fin 2) else 1) =
        (if z.val + 1 ≤ k - 1 ∨ k^2 ≤ z.val + 1 then (0 : Fin 2) else 1) ∧
      (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1 := ⟨schur_two_upper_bound k hk, schur_two_lower_bound k hk⟩
