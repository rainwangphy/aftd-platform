import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallLeft
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallRight

/-!
# cycle_power_dyadic_domain_wall_exact

Topic: combinatorics   Node: 1711f84d12b0

Provenance: helper lemma. OP-205 / RT-1 structural-hypothesis audit following arXiv:2610.15635. A compact five-exception version of the previously computed nonperiodic domain wall6554 was independently audited in experiment7315. This formal countermodel addresses a stronger auxiliary statement without counts or periodicity; it is not a graph cover, a periodic model, an OP-205 refutation, or a research advance.

Every dyadic long-distance edge has exactly one root owner in the explicit radius-eight model, at every integer vertex.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_domain_wall_exact
    (j : ℕ) (hj : j < 3) (v : ℤ) :
    (range (2^j)).sum (fun a =>
      (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
        cycle_power_dyadic_domain_wall (v-(a : ℤ)) (a+8-2^j)).toNat) = 1 := by
  interval_cases j
  · by_cases hL : v ≤ -4
    · generalize hr : v % 4 = r
      have hr0 : 0 ≤ r := by omega
      have hr4 : r < 4 := by omega
      let f : ℕ → ℕ → Bool := fun a b => (if (r-(a : ℤ)) % 2 = 0 then 129 else 243 : ℕ).testBit b
      have hx (a : ℕ) (ha : a < 8) (b : ℕ) :
          cycle_power_dyadic_domain_wall (v-(a : ℤ)) b = f a b := by
        rw [cycle_power_dyadic_domain_wall_left (v-(a : ℤ)) (by omega) b]
        have he : (v-(a : ℤ)) % 2 = (r-(a : ℤ)) % 2 := by omega
        rw [he]
      have heq (N : ℕ) (hN : N ≤ 8) (g : ℕ → ℕ) :
          (range N).sum (fun a =>
            (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
              cycle_power_dyadic_domain_wall (v-(a : ℤ)) (g a)).toNat) =
            (range N).sum (fun a => (f a a && f a (g a)).toNat) := by
        apply sum_congr rfl
        intro a ha
        have ha8 : a < 8 := lt_of_lt_of_le (mem_range.mp ha) hN
        rw [hx a ha8 a, hx a ha8 (g a)]
      rw [heq (2^0) (by norm_num) (fun a => a+8-2^0)]
      dsimp only [f]
      interval_cases r <;> decide
    · by_cases hR : 11 ≤ v
      · generalize hr : v % 4 = r
        have hr0 : 0 ≤ r := by omega
        have hr4 : r < 4 := by omega
        let f : ℕ → ℕ → Bool := fun a b => (if (r-(a : ℤ)) % 4 = 1 then 195 else if (r-(a : ℤ)) % 4 = 3 then 255 else 129 : ℕ).testBit b
        have hx (a : ℕ) (ha : a < 8) (b : ℕ) :
            cycle_power_dyadic_domain_wall (v-(a : ℤ)) b = f a b := by
          rw [cycle_power_dyadic_domain_wall_right (v-(a : ℤ)) (by omega) b]
          have he : (v-(a : ℤ)) % 4 = (r-(a : ℤ)) % 4 := by omega
          rw [he]
        have heq (N : ℕ) (hN : N ≤ 8) (g : ℕ → ℕ) :
            (range N).sum (fun a =>
              (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
                cycle_power_dyadic_domain_wall (v-(a : ℤ)) (g a)).toNat) =
              (range N).sum (fun a => (f a a && f a (g a)).toNat) := by
          apply sum_congr rfl
          intro a ha
          have ha8 : a < 8 := lt_of_lt_of_le (mem_range.mp ha) hN
          rw [hx a ha8 a, hx a ha8 (g a)]
        rw [heq (2^0) (by norm_num) (fun a => a+8-2^0)]
        dsimp only [f]
        interval_cases r <;> decide
      · have hlo : -3 ≤ v := by omega
        have hhi : v ≤ 10 := by omega
        interval_cases v <;> decide
  · by_cases hL : v ≤ -4
    · generalize hr : v % 4 = r
      have hr0 : 0 ≤ r := by omega
      have hr4 : r < 4 := by omega
      let f : ℕ → ℕ → Bool := fun a b => (if (r-(a : ℤ)) % 2 = 0 then 129 else 243 : ℕ).testBit b
      have hx (a : ℕ) (ha : a < 8) (b : ℕ) :
          cycle_power_dyadic_domain_wall (v-(a : ℤ)) b = f a b := by
        rw [cycle_power_dyadic_domain_wall_left (v-(a : ℤ)) (by omega) b]
        have he : (v-(a : ℤ)) % 2 = (r-(a : ℤ)) % 2 := by omega
        rw [he]
      have heq (N : ℕ) (hN : N ≤ 8) (g : ℕ → ℕ) :
          (range N).sum (fun a =>
            (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
              cycle_power_dyadic_domain_wall (v-(a : ℤ)) (g a)).toNat) =
            (range N).sum (fun a => (f a a && f a (g a)).toNat) := by
        apply sum_congr rfl
        intro a ha
        have ha8 : a < 8 := lt_of_lt_of_le (mem_range.mp ha) hN
        rw [hx a ha8 a, hx a ha8 (g a)]
      rw [heq (2^1) (by norm_num) (fun a => a+8-2^1)]
      dsimp only [f]
      interval_cases r <;> decide
    · by_cases hR : 11 ≤ v
      · generalize hr : v % 4 = r
        have hr0 : 0 ≤ r := by omega
        have hr4 : r < 4 := by omega
        let f : ℕ → ℕ → Bool := fun a b => (if (r-(a : ℤ)) % 4 = 1 then 195 else if (r-(a : ℤ)) % 4 = 3 then 255 else 129 : ℕ).testBit b
        have hx (a : ℕ) (ha : a < 8) (b : ℕ) :
            cycle_power_dyadic_domain_wall (v-(a : ℤ)) b = f a b := by
          rw [cycle_power_dyadic_domain_wall_right (v-(a : ℤ)) (by omega) b]
          have he : (v-(a : ℤ)) % 4 = (r-(a : ℤ)) % 4 := by omega
          rw [he]
        have heq (N : ℕ) (hN : N ≤ 8) (g : ℕ → ℕ) :
            (range N).sum (fun a =>
              (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
                cycle_power_dyadic_domain_wall (v-(a : ℤ)) (g a)).toNat) =
              (range N).sum (fun a => (f a a && f a (g a)).toNat) := by
          apply sum_congr rfl
          intro a ha
          have ha8 : a < 8 := lt_of_lt_of_le (mem_range.mp ha) hN
          rw [hx a ha8 a, hx a ha8 (g a)]
        rw [heq (2^1) (by norm_num) (fun a => a+8-2^1)]
        dsimp only [f]
        interval_cases r <;> decide
      · have hlo : -3 ≤ v := by omega
        have hhi : v ≤ 10 := by omega
        interval_cases v <;> decide
  · by_cases hL : v ≤ -4
    · generalize hr : v % 4 = r
      have hr0 : 0 ≤ r := by omega
      have hr4 : r < 4 := by omega
      let f : ℕ → ℕ → Bool := fun a b => (if (r-(a : ℤ)) % 2 = 0 then 129 else 243 : ℕ).testBit b
      have hx (a : ℕ) (ha : a < 8) (b : ℕ) :
          cycle_power_dyadic_domain_wall (v-(a : ℤ)) b = f a b := by
        rw [cycle_power_dyadic_domain_wall_left (v-(a : ℤ)) (by omega) b]
        have he : (v-(a : ℤ)) % 2 = (r-(a : ℤ)) % 2 := by omega
        rw [he]
      have heq (N : ℕ) (hN : N ≤ 8) (g : ℕ → ℕ) :
          (range N).sum (fun a =>
            (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
              cycle_power_dyadic_domain_wall (v-(a : ℤ)) (g a)).toNat) =
            (range N).sum (fun a => (f a a && f a (g a)).toNat) := by
        apply sum_congr rfl
        intro a ha
        have ha8 : a < 8 := lt_of_lt_of_le (mem_range.mp ha) hN
        rw [hx a ha8 a, hx a ha8 (g a)]
      rw [heq (2^2) (by norm_num) (fun a => a+8-2^2)]
      dsimp only [f]
      interval_cases r <;> decide
    · by_cases hR : 11 ≤ v
      · generalize hr : v % 4 = r
        have hr0 : 0 ≤ r := by omega
        have hr4 : r < 4 := by omega
        let f : ℕ → ℕ → Bool := fun a b => (if (r-(a : ℤ)) % 4 = 1 then 195 else if (r-(a : ℤ)) % 4 = 3 then 255 else 129 : ℕ).testBit b
        have hx (a : ℕ) (ha : a < 8) (b : ℕ) :
            cycle_power_dyadic_domain_wall (v-(a : ℤ)) b = f a b := by
          rw [cycle_power_dyadic_domain_wall_right (v-(a : ℤ)) (by omega) b]
          have he : (v-(a : ℤ)) % 4 = (r-(a : ℤ)) % 4 := by omega
          rw [he]
        have heq (N : ℕ) (hN : N ≤ 8) (g : ℕ → ℕ) :
            (range N).sum (fun a =>
              (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
                cycle_power_dyadic_domain_wall (v-(a : ℤ)) (g a)).toNat) =
              (range N).sum (fun a => (f a a && f a (g a)).toNat) := by
          apply sum_congr rfl
          intro a ha
          have ha8 : a < 8 := lt_of_lt_of_le (mem_range.mp ha) hN
          rw [hx a ha8 a, hx a ha8 (g a)]
        rw [heq (2^2) (by norm_num) (fun a => a+8-2^2)]
        dsimp only [f]
        interval_cases r <;> decide
      · have hlo : -3 ≤ v := by omega
        have hhi : v ≤ 10 := by omega
        interval_cases v <;> decide
