import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicZmodModelTightOfCounts

/-!
# cycle_power_dyadic_periodic_model_tight_of_counts

Topic: combinatorics   Node: dc532e43e9b9

Provenance: helper lemma. Uniform actual-cover extraction for OP-205 / RT-1 following arXiv:2610.15635. The anchored-arc lemma is geometric bookkeeping. The saturation helpers double-count exact dyadic owners and active classes over a period; they do not classify class shapes or settle the graph covering value. No research advance is claimed.

For a positive exponent m, nonzero natural period n, and periodic Boolean profiles indexed by the integers, exact dyadic edge-owner sums of one and exactly m+1 active rooted profiles at every integer force each profile's dyadic class weight to equal its selected-offset count. No ordinary-edge coverage or shape hypothesis is assumed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_periodic_model_tight_of_counts
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (hperiod : ∀ p a, x (p+(n : ℤ)) a = x p a)
    (hcount : ∀ v : ℤ, (range (2^m)).sum
      (fun a => (x (v-(a : ℤ)) a).toNat) = m+1)
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum
      (fun a => (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1) :
    ∀ p : ℤ, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun a => (x p a).toNat) := by
  classical
  let b : ZMod n → ℕ → Bool := fun p a => x (p.val : ℤ) a
  have hval (v : ℤ) (a : ℕ) : b (v : ZMod n) a = x v a := by
    obtain ⟨z, hz⟩ := (ZMod.intCast_eq_iff n v (v : ZMod n)).mp rfl
    have hp : Function.Periodic (fun p : ℤ => x p a) (n : ℤ) := fun p => hperiod p a
    have hh := hp.int_mul z (((v : ZMod n).val : ℤ))
    have he : ((v : ZMod n).val : ℤ)+z*(n : ℤ)=v := by
      calc
        _ = ((v : ZMod n).val : ℤ)+(n : ℤ)*z := by ring
        _ = v := hz.symm
    exact hh.symm.trans (congrArg (fun w : ℤ => x w a) he)
  have hshift (v : ZMod n) (a i : ℕ) :
      b (v-(a : ZMod n)) i = x ((v.val : ℤ)-(a : ℤ)) i := by
    simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] using
      hval ((v.val : ℤ)-(a : ℤ)) i
  have hbc (v : ZMod n) : (range (2^m)).sum (fun a => (b (v-(a : ZMod n)) a).toNat) = m+1 := by
    simp_rw [hshift]
    exact hcount (v.val : ℤ)
  have hbe (j : ℕ) (hj : j < m) (v : ZMod n) : (range (2^j)).sum
      (fun a => (b (v-(a : ZMod n)) a && b (v-(a : ZMod n)) (a+2^m-2^j)).toNat) = 1 := by
    simp_rw [hshift]
    exact hexact j hj (v.val : ℤ)
  have ht := cycle_power_dyadic_zmod_model_tight_of_counts m n hm b hbc hbe
  intro p
  simpa only [cycle_power_dyadic_class_weight, hval] using ht (p : ZMod n)
