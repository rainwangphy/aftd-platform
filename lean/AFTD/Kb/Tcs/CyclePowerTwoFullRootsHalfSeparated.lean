import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique

/-!
# cycle_power_two_full_roots_half_separated

Topic: combinatorics   Node: 3922822c10a8

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

When D is twice R and every distance-R pair has a unique root owner, distinct full classes rooted at zero and a positive g must have g at least R.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_two_full_roots_half_separated
    (D R : ℕ) (hD : D = 2*R) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (range R).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-R)).toNat) = 1)
    (g : ℕ) (hg₀ : 0 < g)
    (hfull₀ : ∀ i < D, x 0 i = true)
    (hfullg : ∀ i < D, x (g : ℤ) i = true) : R ≤ g := by
  by_contra hn
  have hgR : g < R := by omega
  have hgD : g < D := by omega
  have hhiD : g+D-R < D := by omega
  have hRD : D-R < D := by omega
  have he := cycle_power_exact_pair_unique D R x hexact (g : ℤ) g 0 hgR (by omega)
    (by simpa only [sub_self] using hfull₀ g hgD)
    (by simpa only [sub_self] using hfull₀ (g+D-R) hhiD)
    (by simpa only [Nat.cast_zero, sub_zero] using hfullg 0 (by omega))
    (by simpa only [Nat.cast_zero, sub_zero, zero_add] using hfullg (D-R) hRD)
  omega
