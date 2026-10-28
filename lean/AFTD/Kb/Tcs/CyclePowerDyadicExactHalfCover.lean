import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairExists

/-!
# cycle_power_dyadic_exact_half_cover

Topic: combinatorics   Node: fbfb6e228e5c

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Exact dyadic pair ownership supplies a witness covering every edge at half the radius, with the distance normalized to a power of two.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_exact_half_cover
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < k+2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^j)).toNat) = 1) :
    ∀ v : ℤ, ∃ a : ℕ, a < 2^(k+1) ∧ x (v-(a : ℤ)) a = true ∧
      x (v-(a : ℤ)) (a+2^(k+1)) = true := by
  have hD : 2^(k+2) = 2*2^(k+1) := by rw [pow_succ]; omega
  intro v
  obtain ⟨a, ha, h₀, h₁⟩ := cycle_power_exact_pair_exists (2^(k+2)) (2^(k+1)) x
    (hexact (k+1) (by omega)) v
  have he : a+2^(k+2)-2^(k+1) = a+2^(k+1) := by omega
  exact ⟨a, ha, h₀, by simpa only [he] using h₁⟩
