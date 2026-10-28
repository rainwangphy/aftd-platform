import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFullClassInternalExactPairImpossible

/-!
# cycle_power_dyadic_two_full_roots_pair_crosses

Topic: combinatorics   Node: 53a607ff6271

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Between full classes rooted at zero and g with g at most the dyadic radius, every selected dyadic pair of an interior root has its lower absolute endpoint below g and upper absolute endpoint at least the radius.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_two_full_roots_pair_crosses
    (m : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (g : ℕ) (hg : g ≤ 2^m)
    (hfull₀ : ∀ i < 2^m, x 0 i = true)
    (hfullg : ∀ i < 2^m, x (g : ℤ) i = true)
    (r : ℕ) (hr₀ : 0 < r) (hrg : r < g)
    (j : ℕ) (hj : j < m) (a : ℕ) (ha : a < 2^j)
    (h₀ : x (r : ℤ) a = true) (h₁ : x (r : ℤ) (a+2^m-2^j) = true) :
    r+a < g ∧ 2^m ≤ r+(a+2^m-2^j) := by
  have hRD : 2^j ≤ 2^m := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hj)
  have haD : a < 2^m := by omega
  have hbD : a+2^m-2^j < 2^m := by omega
  constructor
  · by_contra hn
    have hlo : (g : ℤ) ≤ (r : ℤ)+(a : ℤ) := by exact_mod_cast (show g ≤ r+a by omega)
    have hhi : (r : ℤ)+((a+2^m-2^j : ℕ) : ℤ) < (g : ℤ)+(2^m : ℕ) := by
      exact_mod_cast (show r+(a+2^m-2^j) < g+2^m by omega)
    exact cycle_power_full_class_internal_exact_pair_impossible (2^m) (2^j) hRD x
      (hexact j hj) (r : ℤ) (g : ℤ) (by exact_mod_cast (ne_of_lt hrg))
      hfullg a ha h₀ h₁ hlo hhi
  · by_contra hn
    have hlo : (0 : ℤ) ≤ (r : ℤ)+(a : ℤ) := by positivity
    have hhi : (r : ℤ)+((a+2^m-2^j : ℕ) : ℤ) < (0 : ℤ)+(2^m : ℕ) := by
      simp only [zero_add]
      exact_mod_cast (show r+(a+2^m-2^j) < 2^m by omega)
    exact cycle_power_full_class_internal_exact_pair_impossible (2^m) (2^j) hRD x
      (hexact j hj) (r : ℤ) 0 (by exact_mod_cast (Nat.ne_of_gt hr₀))
      hfull₀ a ha h₀ h₁ hlo hhi
