import AFTD.Prelude

/-!
# cycle_power_dyadic_exact_endpoints

Topic: combinatorics   Node: 1abea431b1cc

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Exact ownership of all dyadic distances in a radius-2^m model with positive exponent forces both endpoints of every rooted class to be selected.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_exact_endpoints
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1) :
    ∀ p : ℤ, x p 0 = true ∧ x p (2^m-1) = true := by
  intro p
  have he := hexact 0 (by omega) p
  simp only [pow_zero, sum_range_one, Nat.cast_zero, sub_zero, zero_add] at he
  cases h₀ : x p 0 <;> cases h₁ : x p (2^m-1) <;> simp [h₀,h₁] at he ⊢
