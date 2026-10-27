import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneOuter
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_full_prune_root_separation

Topic: combinatorics   Node: 3872250e07e2

Provenance: helper lemma. Uniform conditional structural lemmas for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The class no-island hypothesis remains explicit; its derivation from an actual optimal covering model is unresolved. No graph covering value or research advance is claimed.

Two roots whose pruned classes are full must be separated by at least one quarter of the original radius.
-/

open Finset

theorem cycle_power_dyadic_full_prune_root_separation
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (range (2^k)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^k)).toNat) = 1)
    (p : ℤ) (r : ℕ) (hr : 0 < r)
    (hp : ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true)
    (hs : ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x (p+(r : ℤ))) i = true) :
    2^k ≤ r := by
  by_contra hne
  have hH : 2^(k+1)=2*2^k := by rw [pow_succ]; omega
  have hD : 2^(k+2)=4*2^k := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  have ho := cycle_power_dyadic_full_prune_outer k (x p) hp
  have hs' := cycle_power_dyadic_full_prune_outer k (x (p+(r : ℤ))) hs
  have he0 : r+2^(k+2)-2^k=r+3*2^k := by omega
  have he1 : 0+2^(k+2)-2^k=3*2^k := by omega
  have hd := cycle_power_exact_pair_unique (2^(k+2)) (2^k) x hexact
    (p+(r : ℤ)) r 0 (by omega) (Nat.two_pow_pos _)
    (by simpa using ho.1 r (by omega))
    (by simpa only [add_sub_cancel_right,he0] using ho.2 (r+3*2^k) (by omega) (by omega))
    (by simpa using hs'.1 0 (Nat.two_pow_pos _))
    (by simpa only [Nat.cast_zero,sub_zero,he1] using hs'.2 (3*2^k) (by omega) (by omega))
  omega
