import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.ZmodSumSubEqSum
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightEqOfSumEq

/-!
# cycle_power_dyadic_zmod_model_tight_of_counts

Topic: combinatorics   Node: 421a82631322

Provenance: helper lemma. Uniform actual-cover extraction for OP-205 / RT-1 following arXiv:2610.15635. The anchored-arc lemma is geometric bookkeeping. The saturation helpers double-count exact dyadic owners and active classes over a period; they do not classify class shapes or settle the graph covering value. No research advance is claimed.

For a positive exponent m, nonzero natural period n, and Boolean profiles indexed by ZMod n, exact dyadic edge-owner sums of one and exactly m+1 active rooted profiles at each residue force each profile's dyadic class weight to equal its selected-offset count. No ordinary-edge coverage or shape hypothesis is assumed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_zmod_model_tight_of_counts
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m) (b : ZMod n → ℕ → Bool)
    (hcount : ∀ v : ZMod n, (range (2^m)).sum
      (fun a => (b (v-(a : ZMod n)) a).toNat) = m+1)
    (hexact : ∀ j < m, ∀ v : ZMod n, (range (2^j)).sum
      (fun a => (b (v-(a : ZMod n)) a && b (v-(a : ZMod n)) (a+2^m-2^j)).toNat) = 1) :
    ∀ p : ZMod n, cycle_power_dyadic_class_weight m (b p) =
      (range (2^m)).sum (fun a => (b p a).toNat) := by
  classical
  let N : ℕ → ZMod n → ℕ := fun j p => (range (2^j)).sum
    (fun a => (b p a && b p (a+2^m-2^j)).toNat)
  have hN (j : ℕ) (hj : j < m) : (∑ p : ZMod n, N j p) = n := by
    dsimp only [N]
    rw [sum_comm]
    calc
      _ = ∑ a ∈ range (2^j), ∑ v : ZMod n,
          (b (v-(a : ZMod n)) a && b (v-(a : ZMod n)) (a+2^m-2^j)).toNat := by
        apply sum_congr rfl
        intro a ha
        exact zmod_sum_sub_eq_sum n _ (a : ZMod n)
      _ = ∑ v : ZMod n, ∑ a ∈ range (2^j),
          (b (v-(a : ZMod n)) a && b (v-(a : ZMod n)) (a+2^m-2^j)).toNat := sum_comm
      _ = ∑ v : ZMod n, 1 := by simp_rw [hexact j hj]
      _ = n := by simp
  have hw (p : ZMod n) : cycle_power_dyadic_class_weight m (b p) =
      2*N 0 p+(range m).sum (fun j => if j=0 then 0 else N j p) := by
    simp only [cycle_power_dyadic_class_weight, N, pow_zero, sum_range_one, Nat.zero_add]
  have hW : (∑ p : ZMod n, cycle_power_dyadic_class_weight m (b p)) = (m+1)*n := by
    simp_rw [hw]
    rw [sum_add_distrib, ← mul_sum, hN 0 (by omega), sum_comm]
    have he : (range m).sum (fun j => ∑ p : ZMod n, if j=0 then 0 else N j p) =
        (range m).sum (fun j => if j=0 then 0 else n) := by
      apply sum_congr rfl
      intro j hj
      by_cases hj0 : j=0
      · simp only [hj0, ↓reduceIte, sum_const_zero]
      · simp only [hj0, ↓reduceIte]
        exact hN j (mem_range.mp hj)
    rw [he]
    obtain ⟨k, rfl⟩ : ∃ k, m=k+1 := ⟨m-1, by omega⟩
    simp [sum_range_succ', Nat.add_mul] <;> omega
  have hC : (∑ p : ZMod n, (range (2^m)).sum (fun a => (b p a).toNat)) = (m+1)*n := by
    rw [sum_comm]
    calc
      _ = ∑ a ∈ range (2^m), ∑ v : ZMod n, (b (v-(a : ZMod n)) a).toNat := by
        apply sum_congr rfl
        intro a ha
        exact zmod_sum_sub_eq_sum n _ (a : ZMod n)
      _ = ∑ v : ZMod n, ∑ a ∈ range (2^m), (b (v-(a : ZMod n)) a).toNat := sum_comm
      _ = ∑ v : ZMod n, (m+1) := by simp_rw [hcount]
      _ = (m+1)*n := by simp [Nat.mul_comm]
  exact cycle_power_dyadic_class_weight_eq_of_sum_eq m n hm b (hW.trans hC.symm)
