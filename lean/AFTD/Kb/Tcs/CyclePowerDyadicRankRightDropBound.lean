import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicRankCountBalance

/-!
# cycle_power_dyadic_rank_right_drop_bound

Topic: combinatorics   Node: 782ab2a26269

Provenance: helper lemma. Uniform rank-coupling bookkeeping for OP-205 / RT-1, following arXiv:2610.15635. This is an auxiliary consequence of exact dyadic coverage and one neighbouring ordinary distance, not a research advance.

Coverage one step above a dyadic long distance bounds the drop in right-block occupancy by the old boundary-pair bit, after accounting for the two endpoint bits. The statement holds at every rank and arbitrary dyadic radius.
-/

theorem cycle_power_dyadic_rank_right_drop_bound
    (m j : ℕ) (hj : 1 ≤ j) (hjm : j < m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (Finset.range (2 ^ m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ v : ℤ, (Finset.range (2 ^ j)).sum (fun a =>
      (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1)
    (hcover : ∀ v : ℤ, ∃ a : ℕ, a < 2 ^ j - 1 ∧
      x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + (2 ^ m - 2 ^ j + 1)) = true) :
    let q := 2 ^ (j - 1)
    let d := 2 ^ m - 2 ^ j
    ∀ v : ℤ,
      (Finset.range q).sum (fun a => (x (v - (a : ℤ)) (d + a)).toNat) +
        (x (v + 1) d).toNat +
        (x (v - ((2 * q - 1 : ℕ) : ℤ)) (2 * q - 1)).toNat ≤
      (Finset.range q).sum (fun a => (x (v + 1 - (a : ℤ)) (d + a)).toNat) +
        (x (v - ((q - 1 : ℕ) : ℤ)) (q - 1) &&
          x (v - ((q - 1 : ℕ) : ℤ)) (2 ^ m - q)).toNat := by
  intro q d v
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hj1 : 2 ^ j = 2 * q := by
    change 2 ^ j = 2 * 2 ^ (j - 1)
    conv_lhs => rw [← Nat.sub_add_cancel hj]
    rw [pow_succ]
    ring
  let L := (Finset.range q).sum (fun a => (x (v - ((q + a : ℕ) : ℤ)) (q + a)).toNat)
  let R := (Finset.range q).sum (fun a => (x (v - (a : ℤ)) (d + a)).toNat)
  let Lpre := (Finset.range (q - 1)).sum (fun a => (x (v - ((q + a : ℕ) : ℤ)) (q + a)).toNat)
  let Rtail := (Finset.range (q - 1)).sum (fun a => (x (v - (a : ℤ)) (d + 1 + a)).toNat)
  let A := (x (v - ((2 * q - 1 : ℕ) : ℤ)) (2 * q - 1)).toNat
  let B := (x (v + 1) d).toNat
  let C := (x (v - ((q - 1 : ℕ) : ℤ)) (q - 1) &&
        x (v - ((q - 1 : ℕ) : ℤ)) (2 ^ m - q)).toNat
  let R_next := (Finset.range q).sum (fun a => (x (v + 1 - (a : ℤ)) (d + a)).toNat)

  -- L + R = 1
  have hbal : L + R = 1 := by
    have hbal0 := cycle_power_dyadic_rank_count_balance m j hj hjm x htight hexact v
    have h_summand : ∀ a, (x (v + ((2 ^ m - 2 ^ j : ℕ) : ℤ) - ((2 ^ m - 2 ^ j + a : ℕ) : ℤ)) (2 ^ m - 2 ^ j + a)).toNat =
        (x (v - (a : ℤ)) (d + a)).toNat := by
      intro a
      have h1 : ((2 ^ m - 2 ^ j + a : ℕ) : ℤ) = (d : ℤ) + (a : ℤ) := by
        change (((d + a : ℕ) : ℤ)) = (d : ℤ) + (a : ℤ)
        exact Nat.cast_add d a
      have h2 : v + ((2 ^ m - 2 ^ j : ℕ) : ℤ) - ((2 ^ m - 2 ^ j + a : ℕ) : ℤ) = v - (a : ℤ) := by
        change v + (d : ℤ) - ((2 ^ m - 2 ^ j + a : ℕ) : ℤ) = v - (a : ℤ)
        rw [h1]
        ring
      have h3 : 2 ^ m - 2 ^ j + a = d + a := rfl
      rw [h2, h3]
    have hR_eq : (Finset.range (2 ^ (j - 1))).sum (fun a =>
        (x (v + ((2 ^ m - 2 ^ j : ℕ) : ℤ) - ((2 ^ m - 2 ^ j + a : ℕ) : ℤ)) (2 ^ m - 2 ^ j + a)).toNat) = R :=
      Finset.sum_congr rfl (fun a _ => h_summand a)
    change L + _ = 1 at hbal0
    rw [hR_eq] at hbal0
    exact hbal0

  -- L = Lpre + A
  have hL : L = Lpre + A := by
    have hq_eq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq1).symm
    change (Finset.range q).sum _ = Lpre + A
    nth_rw 1 [hq_eq]
    rw [Finset.sum_range_succ]
    have h_arg : q + (q - 1) = 2 * q - 1 := by omega
    have h_term : (x (v - ((q + (q - 1) : ℕ) : ℤ)) (q + (q - 1))).toNat = A := by
      have : (q + (q - 1) : ℕ) = 2 * q - 1 := h_arg
      have hcast : ((q + (q - 1) : ℕ) : ℤ) = ((2 * q - 1 : ℕ) : ℤ) := by rw [this]
      rw [hcast, this]
    rw [h_term]

  -- R_next = B + Rtail
  have hR_next : R_next = B + Rtail := by
    have hq_eq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq1).symm
    change (Finset.range q).sum _ = B + Rtail
    nth_rw 1 [hq_eq]
    rw [Finset.sum_range_succ']
    have h0 : (x (v + 1 - ((0 : ℕ) : ℤ)) (d + 0)).toNat = B := by
      have : v + 1 - ((0 : ℕ) : ℤ) = v + 1 := by push_cast; ring
      have : d + 0 = d := rfl
      rw [‹v + 1 - ((0 : ℕ) : ℤ) = v + 1›, ‹d + 0 = d›]
    have hsucc : ∀ a, (x (v + 1 - ((a + 1 : ℕ) : ℤ)) (d + (a + 1))).toNat =
        (x (v - (a : ℤ)) (d + 1 + a)).toNat := by
      intro a
      have : v + 1 - ((a + 1 : ℕ) : ℤ) = v - (a : ℤ) := by push_cast; ring
      have : d + (a + 1) = d + 1 + a := by omega
      rw [‹v + 1 - ((a + 1 : ℕ) : ℤ) = v - (a : ℤ)›, ‹d + (a + 1) = d + 1 + a›]
    rw [h0, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => hsucc a)

  -- 1 ≤ Lpre + Rtail + C
  have hcov : 1 ≤ Lpre + Rtail + C := by
    obtain ⟨a, ha_lt, hx1, hx2⟩ := hcover v
    rw [hj1] at ha_lt
    rcases lt_trichotomy a (q - 1) with h_lt | h_eq | h_gt
    · -- Case 1: a < q - 1
      have ha_mem : a ∈ Finset.range (q - 1) := Finset.mem_range.mpr h_lt
      have h_term : (x (v - (a : ℤ)) (d + 1 + a)).toNat = 1 := by
        have hd_eq : d + 1 + a = a + (2 ^ m - 2 ^ j + 1) := by
          change (2 ^ m - 2 ^ j) + 1 + a = a + (2 ^ m - 2 ^ j + 1)
          omega
        rw [hd_eq, hx2]
        rfl
      have h_le : (x (v - (a : ℤ)) (d + 1 + a)).toNat ≤ Rtail :=
        Finset.single_le_sum (f := fun (k : ℕ) => (x (v - (k : ℤ)) (d + 1 + k)).toNat)
          (fun _ _ => Nat.zero_le _) ha_mem
      omega
    · -- Case 2: a = q - 1
      have hqm : 2 * q ≤ 2 ^ m := by
        rw [← hj1]
        exact Nat.pow_le_pow_right (by decide) (le_of_lt hjm)
      have hd_eq : (q - 1) + (2 ^ m - 2 ^ j + 1) = 2 ^ m - q := by
        rw [hj1]
        omega
      have hx2' : x (v - ((q - 1 : ℕ) : ℤ)) (2 ^ m - q) = true := by
        have := hx2
        rw [h_eq] at this
        rwa [hd_eq] at this
      have hx1' : x (v - ((q - 1 : ℕ) : ℤ)) (q - 1) = true := by
        rwa [h_eq] at hx1
      have hC : C = 1 := by
        change (x (v - ((q - 1 : ℕ) : ℤ)) (q - 1) && x (v - ((q - 1 : ℕ) : ℤ)) (2 ^ m - q)).toNat = 1
        rw [hx1', hx2']
        rfl
      omega
    · -- Case 3: q ≤ a
      have h_q_le_a : q ≤ a := by omega
      let k := a - q
      have hk_lt : k < q - 1 := by omega
      have hk_mem : k ∈ Finset.range (q - 1) := Finset.mem_range.mpr hk_lt
      have h_qk : q + k = a := by omega
      have h_term : (x (v - ((q + k : ℕ) : ℤ)) (q + k)).toNat = 1 := by
        have : (q + k : ℕ) = a := h_qk
        have h1 : ((q + k : ℕ) : ℤ) = (a : ℤ) := by rw [this]
        rw [h1, this, hx1]
        rfl
      have h_le : (x (v - ((q + k : ℕ) : ℤ)) (q + k)).toNat ≤ Lpre :=
        Finset.single_le_sum (f := fun (k : ℕ) => (x (v - ((q + k : ℕ) : ℤ)) (q + k)).toNat)
          (fun _ _ => Nat.zero_le _) hk_mem
      omega

  -- Final combination
  change R + B + A ≤ R_next + C
  omega
