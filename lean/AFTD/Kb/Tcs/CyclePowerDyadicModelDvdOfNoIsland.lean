import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicModelDvdOfEndpointOverlap
import AFTD.Kb.Tcs.CyclePowerDyadicEndpointOverlapOfNoIsland
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_model_dvd_of_no_island

Topic: combinatorics   Node: 281d6b14ee9d

Provenance: helper lemma. Conditional assembly for OP-205 / RT-1 following arXiv:2610.15635 Section 3. This combines the uniform no-island endpoint-overlap theorem, label-period divisibility, and the central-occurrence argument; no actual-cover shape classification or main covering-number theorem is claimed.

A periodic optimally counted tight dyadic class model with proper class labels, exact dyadic edges and full ordinary coverage has period divisible by its radius, provided every class is the union of an initial and terminal interval. The no-island shape assumption is explicit and remains the structural bottleneck.
-/

open Finset

theorem cycle_power_dyadic_model_dvd_of_no_island
    (m n : ℕ) (hm : 2 ≤ m) (hn : 0 < n)
    (x : ℤ → ℕ → Bool) (ell : ℤ → Fin (m+1))
    (hperiod : ∀ p a, x (p+(n : ℤ)) a = x p a)
    (hell : ∀ p, ell (p+(n : ℤ)) = ell p)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun a => (x p a).toNat))
    (hcount : ∀ v : ℤ, (range (2^m)).sum
      (fun a => (x (v-(a : ℤ)) a).toNat) = m+1)
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hsep : ∀ (v : ℤ) (a b : ℕ), a < 2^m → b < 2^m → a ≠ b →
      x (v-(a : ℤ)) a = true → x (v-(b : ℤ)) b = true →
        ell (v-(a : ℤ)) ≠ ell (v-(b : ℤ)))
    (hshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      x p a = false → x p b = true → x p c = true) :
    2^m ∣ n := by
  apply cycle_power_dyadic_model_dvd_of_endpoint_overlap m n hm hn x ell
    hperiod hell htight hcount hexact hcover hsep
  exact cycle_power_dyadic_endpoint_overlap_of_no_island m (by omega) x htight hexact hcover hshape
