import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_half_owner_full_prune_of_middle

Topic: combinatorics   Node: 9deb58356c2e

Provenance: helper lemma. Uniform conditional structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The middle-bit fullness assumptions and smaller-quarter monotonicity are explicit when used; no optimal-count classification, graph covering value or research advance is claimed.

If every selected middle-quarter bit forces a full prune, then every class owning a half-radius edge has a full prune.
-/

open Finset

theorem cycle_power_dyadic_half_owner_full_prune_of_middle
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (hmid : ∀ (p : ℤ) (a : ℕ), 2^k ≤ a → a < 3*2^k → x p a = true →
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true)
    (p : ℤ) (a : ℕ) (ha : a < 2^(k+1))
    (h0 : x p a = true) (h1 : x p (a+2^(k+1)) = true) :
    ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true := by
  have hH : 2^(k+1)=2*2^k := by rw [pow_succ]; omega
  by_cases hl : a < 2^k
  · exact hmid p (a+2^(k+1)) (by omega) (by omega) h1
  · exact hmid p a (by omega) (by omega) h0
