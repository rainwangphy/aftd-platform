import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique

/-!
# cycle_power_full_class_internal_exact_pair_impossible

Topic: combinatorics   Node: fd473e4fcc6e

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

In an integer rooted-class system with exact distance D-R edge ownership, a selected distance D-R pair in one root cannot lie wholly in a distinct full radius-D class.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_full_class_internal_exact_pair_impossible
    (D R : ℕ) (hRD : R ≤ D) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (range R).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-R)).toNat) = 1)
    (p q : ℤ) (hpq : p ≠ q) (hfull : ∀ i < D, x q i = true)
    (a : ℕ) (ha : a < R) (h₀ : x p a = true) (h₁ : x p (a+D-R) = true)
    (hlo : q ≤ p+(a : ℤ)) (hhi : p+((a+D-R : ℕ) : ℤ) < q+(D : ℤ)) : False := by
  let b := (p+(a : ℤ)-q).toNat
  have hbcast : (b : ℤ) = p+(a : ℤ)-q := Int.toNat_of_nonneg (by omega)
  have hRDa : R ≤ a+D := by omega
  have hcast : ((a+D-R : ℕ) : ℤ) = (a : ℤ)+D-R := by
    rw [Nat.cast_sub hRDa, Nat.cast_add]
  have hb : b < R := by omega
  have hbD : b < D := by omega
  have hb1D : b+D-R < D := by omega
  have hp : p+(a : ℤ)-(a : ℤ) = p := by omega
  have hq : p+(a : ℤ)-(b : ℤ) = q := by omega
  have he := cycle_power_exact_pair_unique D R x hexact (p+(a : ℤ)) a b ha hb
    (by simpa only [hp] using h₀) (by simpa only [hp] using h₁)
    (by simpa only [hq] using hfull b hbD)
    (by simpa only [hq] using hfull (b+D-R) hb1D)
  apply hpq
  omega
