import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_full_prune_outer

Topic: combinatorics   Node: a0821749d8d7

Provenance: helper lemma. Uniform conditional structural lemmas for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The class no-island hypothesis remains explicit; its derivation from an actual optimal covering model is unresolved. No graph covering value or research advance is claimed.

Fullness after middle-quarter pruning means that both outer quarters of the original class are entirely selected.
-/

open Finset

theorem cycle_power_dyadic_full_prune_outer
    (k : ℕ) (b : ℕ → Bool)
    (hfull : ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k b i = true) :
    (∀ i < 2^k, b i = true) ∧
    (∀ i, 3*2^k ≤ i → i < 2^(k+2) → b i = true) := by
  have hH : 2^(k+1)=2*2^k := by rw [pow_succ]; omega
  have hD : 2^(k+2)=4*2^k := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  constructor
  · intro i hi
    have hh := hfull i (by omega)
    dsimp [cycle_power_dyadic_b_lift] at hh
    rwa [if_pos hi] at hh
  · intro i hi0 hi1
    have hh := hfull (i-2^(k+1)) (by omega)
    dsimp [cycle_power_dyadic_b_lift] at hh
    rw [if_neg (by omega)] at hh
    have he : i-2^(k+1)+2^(k+1)=i := by omega
    rwa [he] at hh
