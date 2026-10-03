import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionLymSumLe
import AFTD.Kb.GameTheoryEconomics.PersuasionChooseMulChooseLeTwo

/-!
# persuasion_half_weight_sum_le

Topic: mechanism_design   Node: 023bee4aee7a

Half-weight sets. For nonnegative weights w on Fin (2m+1) with positive total W, summing over the zero-weight points e the number of m-subsets avoiding e of weight exactly W/2 gives at most m · C(2m, m).
-/

open Finset in
/-- **Half-weight sets.** For nonnegative weights `w` on `Fin (2m+1)` with positive total `W`,
summing over the zero-weight points `e` the number of `m`-subsets avoiding `e` of weight exactly
`W/2` gives at most `m · C(2m, m)`. -/
lemma persuasion_half_weight_sum_le (m : ℕ) (hm : 1 ≤ m) (w : Fin (2 * m + 1) → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hW : 0 < ∑ j, w j) :
    ∑ e ∈ Finset.univ.filter (fun e => w e = 0),
      ((powersetCard m (Finset.univ.erase e)).filter
        (fun i => 2 * ∑ j ∈ i, w j = ∑ j, w j)).card ≤ m * (2 * m).choose m := by
  classical
  set W := ∑ j, w j with hWdef
  set Z := Finset.univ.filter (fun e => w e = 0) with hZdef
  set U := Finset.univ.filter (fun e => w e ≠ 0) with hUdef
  have hZU : Z.card + U.card = 2 * m + 1 := by
    have := card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * m + 1)))) (p := fun e => w e = 0)
    simpa [Z, U] using this
  have hcardS : ∀ e, ((powersetCard m (Finset.univ.erase e)).filter
      (fun i => 2 * ∑ j ∈ i, w j = W)).card ≤ (2 * m).choose m := by
    intro e
    calc _ ≤ (powersetCard m (Finset.univ.erase e)).card := card_filter_le _ _
      _ = (2 * m).choose m := by
        rw [card_powersetCard, card_erase_of_mem (Finset.mem_univ e), card_univ, Fintype.card_fin]
        rfl
  by_cases hZ : Z.card ≤ m
  · calc _ ≤ ∑ e ∈ Z, (2 * m).choose m := sum_le_sum (fun e _ => hcardS e)
      _ = Z.card * (2 * m).choose m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m * (2 * m).choose m := Nat.mul_le_mul_right _ hZ
  push Not at hZ
  have hu : U.card ≤ m := by omega
  set PP := U.powerset.filter (fun T => 2 * ∑ j ∈ T, w j = W) with hPP
  have hwU : ∀ i : Finset (Fin (2 * m + 1)), ∑ j ∈ i, w j = ∑ j ∈ i ∩ U, w j := by
    intro i
    have : i ∩ U = i.filter (fun j => w j ≠ 0) := by
      ext j; simp [U]
    rw [this, sum_filter_ne_zero]
  have hUW : ∑ j ∈ U, w j = W := by
    rw [hWdef, hwU Finset.univ, Finset.univ_inter]
  have hPbounds : ∀ T ∈ PP, 1 ≤ T.card ∧ T.card + 1 ≤ U.card := by
    intro T hT
    rw [hPP, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTU, hTw⟩ := hT
    constructor
    · rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [card_eq_zero] at h0
      subst h0
      simp at hTw
      linarith
    · have hne : T ≠ U := by
        intro h
        subst h
        linarith
      have := card_lt_card (ssubset_of_subset_of_ne hTU hne)
      omega
  have hanti : IsAntichain (· ⊆ ·) (PP : Set (Finset (Fin (2 * m + 1)))) := by
    intro T hT T' hT' hne hsub
    rw [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_powerset] at hT hT'
    obtain ⟨x, hxT', hxT⟩ := Finset.exists_of_ssubset (ssubset_of_subset_of_ne hsub hne)
    have hxU : w x ≠ 0 := by
      have := hT'.1 hxT'
      simpa [U] using this
    have hpos : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hxU)
    have : ∑ j ∈ T, w j + w x ≤ ∑ j ∈ T', w j := by
      rw [add_comm, ← sum_insert hxT]
      exact sum_le_sum_of_subset_of_nonneg (Finset.insert_subset hxT' hsub) (fun j _ _ => hw j)
    linarith [hT.2, hT'.2]
  have hper : ∀ e ∈ Z, ((powersetCard m (Finset.univ.erase e)).filter
      (fun i => 2 * ∑ j ∈ i, w j = W)).card
        ≤ ∑ T ∈ PP, (2 * m - U.card).choose (m - T.card) := by
    intro e he
    have heZ : w e = 0 := by simpa [Z] using he
    rw [card_eq_sum_card_fiberwise (f := fun i => i ∩ U) (t := PP)]
    · apply sum_le_sum
      intro T hT
      calc _ ≤ (powersetCard (m - T.card) (Z.erase e)).card := by
            apply card_le_card_of_injOn (fun i => i \ U)
            · intro i hi
              rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, mem_powersetCard] at hi
              obtain ⟨⟨⟨hie, hic⟩, -⟩, hiT⟩ := hi
              rw [Finset.mem_coe, mem_powersetCard]
              constructor
              · intro x hx
                rw [Finset.mem_sdiff] at hx
                have hxe := hie hx.1
                rw [mem_erase] at hxe ⊢
                refine ⟨hxe.1, ?_⟩
                have : ¬ w x ≠ 0 := fun h => hx.2 (by simp [U, h])
                simpa [Z] using this
              · show (i \ U).card = m - T.card
                have h1 := card_sdiff_add_card_inter i U
                rw [hiT, hic] at h1
                omega
            · intro i hi i' hi' h
              rw [Finset.mem_coe, Finset.mem_filter] at hi hi'
              have e1 : i = (i \ U) ∪ (i ∩ U) := (Finset.sdiff_union_inter i U).symm
              have e2 : i' = (i' \ U) ∪ (i' ∩ U) := (Finset.sdiff_union_inter i' U).symm
              have h' : i \ U = i' \ U := h
              rw [e1, e2, hi.2, hi'.2, h']
        _ = (2 * m - U.card).choose (m - T.card) := by
            rw [card_powersetCard, card_erase_of_mem he]
            congr 1
            omega
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter, mem_powersetCard] at hi
      rw [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, by rw [← hwU]; exact hi.2⟩
  rcases PP.eq_empty_or_nonempty with hP0 | ⟨T0, hT0⟩
  · calc _ ≤ ∑ e ∈ Z, 0 := sum_le_sum (fun e he => by
            have := hper e he
            rw [hP0, sum_empty] at this
            exact this)
      _ ≤ m * (2 * m).choose m := by simp
  have hu2 : 2 ≤ U.card := by
    have := hPbounds T0 hT0
    omega
  have hB : ∀ e ∈ Z, ((powersetCard m (Finset.univ.erase e)).filter
      (fun i => 2 * ∑ j ∈ i, w j = W)).card ≤ 2 * (2 * (m - 1)).choose (m - 1) := by
    intro e he
    refine (hper e he).trans ?_
    apply persuasion_lym_sum_le U PP (fun T hT => Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) hanti
      (fun t => (2 * m - U.card).choose (m - t))
    intro T hT
    have hb := hPbounds T hT
    rw [mul_comm]
    exact persuasion_choose_mul_choose_le_two m U.card T.card hu2 hu hb.1 hb.2
  have hZc : Z.card ≤ 2 * m - 1 := by omega
  calc _ ≤ ∑ e ∈ Z, 2 * (2 * (m - 1)).choose (m - 1) := sum_le_sum hB
    _ = Z.card * (2 * (2 * (m - 1)).choose (m - 1)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * m - 1) * (2 * (2 * (m - 1)).choose (m - 1)) := Nat.mul_le_mul_right _ hZc
    _ = m * (2 * m).choose m := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have h := Nat.succ_mul_centralBinom_succ k
        rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
        rw [show k + 1 - 1 = k by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega, h]
        ring
