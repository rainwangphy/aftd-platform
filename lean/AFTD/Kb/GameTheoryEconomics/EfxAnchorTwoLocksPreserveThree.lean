import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAnchorFamilyValues
import AFTD.Kb.GameTheoryEconomics.EfxAnchorFamilyBaseline
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockBaseline

/-!
# efx_anchor_two_locks_preserve_three

Topic: fair_division   Node: 8166ff2582dd

Provenance: helper lemma. Constructive completion for the two-lock OP-7 Pareto obstruction; experiments 11534 and 11536.

In the two-lock anchor family, a complete EFX allocation can preserve the original three agents’ starting utilities for every positive anchor count. The fourth agent necessarily loses, by the separate fourth-loss lemma.
-/

set_option maxHeartbeats 1200000

private def efx_anchor_two_locks_preserve_three_x0 (r : Nat) : Nat :=
  r + (r - 3) / 4 + 1 + (if 1 <= (r - 3) % 4 then 1 else 0)
private def efx_anchor_two_locks_preserve_three_x1 (r : Nat) : Nat :=
  r + (r - 3) / 4 + 1 + (if 2 <= (r - 3) % 4 then 1 else 0)
private def efx_anchor_two_locks_preserve_three_x2 (r : Nat) : Nat :=
  (r - 3) / 4 + 1 + (if (r - 3) % 4 = 3 then 1 else 0)
private def efx_anchor_two_locks_preserve_three_x3 (r : Nat) : Nat := (r - 3) / 4

private def efx_anchor_two_locks_preserve_three_ao (r : Nat) (a : Fin (r+r+r)) : Fin 4 :=
  if a.val < efx_anchor_two_locks_preserve_three_x0 r then 0
  else if a.val < efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r then 1
  else if a.val < efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r then 2
  else 3

private def efx_anchor_two_locks_preserve_three_sg (r : Nat) :
    Fin ((7+(r+r+r))+2) -> Fin 4 :=
  Fin.addCases
    (Fin.addCases (fun _ : Fin 7 => (3 : Fin 4))
      (fun a => efx_anchor_two_locks_preserve_three_ao r a))
    (fun k : Fin 2 => if k.val = 0 then 2 else 3)

private def efx_anchor_two_locks_preserve_three_av (i : Fin 4) : Nat :=
  if i = 3 then 1 else 3000
private def efx_anchor_two_locks_preserve_three_lv (r : Nat) (i : Fin 4) : Nat :=
  if i = 3 then 8 + 3 * r
  else if i = 0 then r * 3000 + 162
  else if i = 1 then r * 3000 + 151
  else r * 3000 + 100
private def efx_anchor_two_locks_preserve_three_os (i : Fin 4) : Nat :=
  if i = 3 then 7 else if i = 0 then 427 else if i = 1 then 317 else 217
private def efx_anchor_two_locks_preserve_three_lbv (i j : Fin 4) : Nat :=
  if i = 3 then 1 else if j = 3 then 1 else 3000
private def efx_anchor_two_locks_preserve_three_bv (r : Nat) (i j : Fin 4) : Nat :=
  if j = 0 then efx_anchor_two_locks_preserve_three_av i
      * efx_anchor_two_locks_preserve_three_x0 r
  else if j = 1 then efx_anchor_two_locks_preserve_three_av i
      * efx_anchor_two_locks_preserve_three_x1 r
  else if j = 2 then efx_anchor_two_locks_preserve_three_av i
      * efx_anchor_two_locks_preserve_three_x2 r
      + efx_anchor_two_locks_preserve_three_lv r i
  else efx_anchor_two_locks_preserve_three_os i
      + efx_anchor_two_locks_preserve_three_av i
        * efx_anchor_two_locks_preserve_three_x3 r
      + efx_anchor_two_locks_preserve_three_lv r i

private lemma efx_anchor_two_locks_preserve_three_real_le_iff {m : Nat}
    (v : Fin m -> Nat) (S : Finset (Fin m)) (B : Nat) :
    (B : Real) <= additive_valuation (fun g => (v g : Real)) S ↔ B <= ∑ g ∈ S, v g := by
  rw [additive_valuation, ← Nat.cast_sum]
  exact Nat.cast_le

private lemma efx_anchor_two_locks_preserve_three_arith (r : Nat) (h3 : 3 <= r) :
    (r + 1 <= efx_anchor_two_locks_preserve_three_x0 r) ∧
    (r + 1 <= efx_anchor_two_locks_preserve_three_x1 r) ∧
    (1 <= efx_anchor_two_locks_preserve_three_x2 r) ∧
    (efx_anchor_two_locks_preserve_three_x2 r + r
      <= efx_anchor_two_locks_preserve_three_x0 r) ∧
    (efx_anchor_two_locks_preserve_three_x2 r + r
      <= efx_anchor_two_locks_preserve_three_x1 r) ∧
    (efx_anchor_two_locks_preserve_three_x1 r
      <= efx_anchor_two_locks_preserve_three_x0 r + 1) ∧
    (efx_anchor_two_locks_preserve_three_x0 r
      <= efx_anchor_two_locks_preserve_three_x1 r + 1) ∧
    (efx_anchor_two_locks_preserve_three_x3 r + r + 1
      <= efx_anchor_two_locks_preserve_three_x0 r) ∧
    (efx_anchor_two_locks_preserve_three_x3 r + r + 1
      <= efx_anchor_two_locks_preserve_three_x1 r) ∧
    (efx_anchor_two_locks_preserve_three_x3 r + 1
      <= efx_anchor_two_locks_preserve_three_x2 r) ∧
    (efx_anchor_two_locks_preserve_three_x2 r
      <= efx_anchor_two_locks_preserve_three_x3 r + 8) ∧
    (efx_anchor_two_locks_preserve_three_x0 r
      <= efx_anchor_two_locks_preserve_three_x2 r + r + 1) ∧
    (efx_anchor_two_locks_preserve_three_x1 r
      <= efx_anchor_two_locks_preserve_three_x2 r + r + 1) := by
  have hd4 : 4 * ((r-3)/4) + (r-3)%4 = r - 3 := Nat.div_add_mod (r-3) 4
  have hd4' : (r - 3) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [efx_anchor_two_locks_preserve_three_x0,
      efx_anchor_two_locks_preserve_three_x1,
      efx_anchor_two_locks_preserve_three_x2,
      efx_anchor_two_locks_preserve_three_x3] <;> split_ifs <;> omega

private lemma efx_anchor_two_locks_preserve_three_bv_efx (r : Nat) (hr : 3 <= r)
    (i j : Fin 4) (hij : i ≠ j) :
    efx_anchor_two_locks_preserve_three_bv r i j
      <= efx_anchor_two_locks_preserve_three_bv r i i
        + efx_anchor_two_locks_preserve_three_lbv i j := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩ :=
    efx_anchor_two_locks_preserve_three_arith r hr
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | (simp [efx_anchor_two_locks_preserve_three_bv,
          efx_anchor_two_locks_preserve_three_av,
          efx_anchor_two_locks_preserve_three_lv,
          efx_anchor_two_locks_preserve_three_os,
          efx_anchor_two_locks_preserve_three_lbv]; nlinarith)

private lemma efx_anchor_two_locks_preserve_three_bv_ir (r : Nat) (hr : 3 <= r)
    (i : Fin 3) :
    efx_anchor_family_baseline r 2 i.castSucc
      <= efx_anchor_two_locks_preserve_three_bv r i.castSucc i.castSucc := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩ :=
    efx_anchor_two_locks_preserve_three_arith r hr
  fin_cases i <;>
    (simp [efx_anchor_two_locks_preserve_three_bv,
      efx_anchor_two_locks_preserve_three_av,
      efx_anchor_two_locks_preserve_three_lv,
      efx_anchor_family_baseline]; nlinarith)

private lemma efx_anchor_two_locks_preserve_three_old (r : Nat) (g : Fin 7) (i : Fin 4) :
    efx_anchor_family_values r 2 i (Fin.castAdd 2 (Fin.castAdd (r+r+r) g))
      = if i = 3 then 1 else efx_pareto_lock_values i g.castSucc := by
  by_cases h : i = 3 <;> simp [efx_anchor_family_values, Fin.addCases_left, h]

private lemma efx_anchor_two_locks_preserve_three_anchor (r : Nat) (a : Fin (r+r+r))
    (i : Fin 4) :
    efx_anchor_family_values r 2 i (Fin.castAdd 2 (Fin.natAdd 7 a))
      = (if i = 3 then 1 else 3000) := by
  by_cases h : i = 3
  · subst h; simp [efx_anchor_family_values, Fin.addCases_left, Fin.addCases_right]
  · simp [efx_anchor_family_values, Fin.addCases_left, Fin.addCases_right, h]

private lemma efx_anchor_two_locks_preserve_three_lockpos :
    ∀ (i : Fin 4) (g : Fin 8), 1 <= efx_pareto_lock_values i g := by decide

private lemma efx_anchor_two_locks_preserve_three_lock (r : Nat) (k : Fin 2) (i : Fin 4) :
    efx_anchor_family_values r 2 i (Fin.natAdd (7+(r+r+r)) k)
      = efx_anchor_two_locks_preserve_three_lv r i := by
  fin_cases i
  · simp [efx_anchor_family_values, Fin.addCases_right,
      efx_anchor_two_locks_preserve_three_lv, efx_pareto_lock_baseline]
  · simp [efx_anchor_family_values, Fin.addCases_right,
      efx_anchor_two_locks_preserve_three_lv, efx_pareto_lock_baseline]
  · simp [efx_anchor_family_values, Fin.addCases_right,
      efx_anchor_two_locks_preserve_three_lv, efx_pareto_lock_baseline]
  · simp [efx_anchor_family_values, Fin.addCases_right,
      efx_anchor_two_locks_preserve_three_lv]

private lemma efx_anchor_two_locks_preserve_three_vpos (r : Nat) (i : Fin 4)
    (g : Fin ((7+(r+r+r))+2)) : 1 <= efx_anchor_family_values r 2 i g := by
  refine Fin.addCases (fun u => ?_) (fun k => ?_) g
  · refine Fin.addCases (fun g => ?_) (fun a => ?_) u
    · rw [efx_anchor_two_locks_preserve_three_old]
      split_ifs with h
      · norm_num
      · exact efx_anchor_two_locks_preserve_three_lockpos i g.castSucc
    · rw [efx_anchor_two_locks_preserve_three_anchor]
      split_ifs with h <;> norm_num
  · rw [efx_anchor_two_locks_preserve_three_lock]
    fin_cases i <;> simp [efx_anchor_two_locks_preserve_three_lv] <;> omega

private lemma efx_anchor_two_locks_preserve_three_vbig (r : Nat) (hr : 1 <= r)
    (i : Fin 4) (hi : i ≠ 3) (g : Fin ((7+(r+r+r))+2))
    (hg : efx_anchor_two_locks_preserve_three_sg r g ≠ 3) :
    3000 <= efx_anchor_family_values r 2 i g := by
  revert hg
  refine Fin.addCases (motive := fun g => efx_anchor_two_locks_preserve_three_sg r g ≠ 3 ->
      3000 <= efx_anchor_family_values r 2 i g) (fun u => ?_) (fun k => ?_) g
  · refine Fin.addCases (motive := fun u =>
        efx_anchor_two_locks_preserve_three_sg r (Fin.castAdd 2 u) ≠ 3 ->
          3000 <= efx_anchor_family_values r 2 i (Fin.castAdd 2 u))
      (fun g => ?_) (fun a => ?_) u
    · intro hg
      exact absurd (by simp [efx_anchor_two_locks_preserve_three_sg,
        Fin.addCases_left] : efx_anchor_two_locks_preserve_three_sg r
          (Fin.castAdd 2 (Fin.castAdd (r+r+r) g)) = 3) hg
    · intro hg
      rw [efx_anchor_two_locks_preserve_three_anchor]
      rw [if_neg hi]
  · intro hg
    rw [efx_anchor_two_locks_preserve_three_lock]
    fin_cases i <;> simp [efx_anchor_two_locks_preserve_three_lv] at * <;> omega

private lemma efx_anchor_two_locks_preserve_three_lb_le (r : Nat) (hr : 1 <= r)
    (i : Fin 4) (g : Fin ((7+(r+r+r))+2)) :
    efx_anchor_two_locks_preserve_three_lbv i
        (efx_anchor_two_locks_preserve_three_sg r g)
      <= efx_anchor_family_values r 2 i g := by
  by_cases hj : efx_anchor_two_locks_preserve_three_sg r g = 3
  · have hl : efx_anchor_two_locks_preserve_three_lbv i
        (efx_anchor_two_locks_preserve_three_sg r g) = 1 := by
      simp [efx_anchor_two_locks_preserve_three_lbv, hj]
    rw [hl]; exact efx_anchor_two_locks_preserve_three_vpos r i g
  · by_cases hi : i = 3
    · have hl : efx_anchor_two_locks_preserve_three_lbv i
          (efx_anchor_two_locks_preserve_three_sg r g) = 1 := by
        simp [efx_anchor_two_locks_preserve_three_lbv, hi]
      rw [hl]; exact efx_anchor_two_locks_preserve_three_vpos r i g
    · have hl : efx_anchor_two_locks_preserve_three_lbv i
          (efx_anchor_two_locks_preserve_three_sg r g) = 3000 := by
        simp [efx_anchor_two_locks_preserve_three_lbv, hi, hj]
      rw [hl]; exact efx_anchor_two_locks_preserve_three_vbig r hr i hi g hj

private lemma efx_anchor_two_locks_preserve_three_sum_lt (n a c : Nat) (ha : a <= n) :
    (∑ x : Fin n, (if x.val < a then c else 0)) = a * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < a then c else 0)]
  have h1 : (∑ k ∈ Finset.range n, (if k < a then c else 0))
      = ∑ k ∈ (Finset.range n).filter (fun k => k < a), c := by rw [Finset.sum_filter]
  rw [h1, Finset.sum_const_nat (m := c) (f := fun _ => c) (by simp)]
  congr 1
  have h2 : (Finset.range n).filter (fun k => k < a) = Finset.range a := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h2, Finset.card_range]

private lemma efx_anchor_two_locks_preserve_three_sum_between (n a b c : Nat)
    (hb : b <= n) :
    (∑ x : Fin n, (if a <= x.val ∧ x.val < b then c else 0)) = (b - a) * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if a <= k ∧ k < b then c else 0)]
  have h1 : (∑ k ∈ Finset.range n, (if a <= k ∧ k < b then c else 0))
      = ∑ k ∈ (Finset.range n).filter (fun k => a <= k ∧ k < b), c := by
    rw [Finset.sum_filter]
  rw [h1, Finset.sum_const_nat (m := c) (f := fun _ => c) (by simp)]
  congr 1
  have h2 : (Finset.range n).filter (fun k => a <= k ∧ k < b) = Finset.Ico a b := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨lt_of_lt_of_le h.2 hb, h⟩
  rw [h2, Nat.card_Ico]

private lemma efx_anchor_two_locks_preserve_three_sum_ge (n a c : Nat) (ha : a <= n) :
    (∑ x : Fin n, (if a <= x.val then c else 0)) = (n - a) * c := by
  have h : (∑ x : Fin n, (if a <= x.val then c else 0))
      = ∑ x : Fin n, (if a <= x.val ∧ x.val < n then c else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    have hx : x.val < n := x.isLt
    by_cases h1 : a <= x.val <;> simp [h1, hx]
  rw [h, efx_anchor_two_locks_preserve_three_sum_between n a n c le_rfl]

private lemma efx_anchor_two_locks_preserve_three_ao0 (r : Nat) (x : Fin (r+r+r)) :
    efx_anchor_two_locks_preserve_three_ao r x = 0 ↔
      x.val < efx_anchor_two_locks_preserve_three_x0 r := by
  unfold efx_anchor_two_locks_preserve_three_ao; split_ifs <;> simp_all

private lemma efx_anchor_two_locks_preserve_three_ao1 (r : Nat) (x : Fin (r+r+r)) :
    efx_anchor_two_locks_preserve_three_ao r x = 1 ↔
      efx_anchor_two_locks_preserve_three_x0 r <= x.val ∧
        x.val < efx_anchor_two_locks_preserve_three_x0 r
          + efx_anchor_two_locks_preserve_three_x1 r := by
  unfold efx_anchor_two_locks_preserve_three_ao; split_ifs <;> simp_all <;> omega

private lemma efx_anchor_two_locks_preserve_three_ao2 (r : Nat) (x : Fin (r+r+r)) :
    efx_anchor_two_locks_preserve_three_ao r x = 2 ↔
      efx_anchor_two_locks_preserve_three_x0 r
          + efx_anchor_two_locks_preserve_three_x1 r <= x.val ∧
        x.val < efx_anchor_two_locks_preserve_three_x0 r
          + efx_anchor_two_locks_preserve_three_x1 r
          + efx_anchor_two_locks_preserve_three_x2 r := by
  unfold efx_anchor_two_locks_preserve_three_ao; split_ifs <;> simp_all <;> omega

private lemma efx_anchor_two_locks_preserve_three_ao3 (r : Nat) (x : Fin (r+r+r)) :
    efx_anchor_two_locks_preserve_three_ao r x = 3 ↔
      efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r
        + efx_anchor_two_locks_preserve_three_x2 r <= x.val := by
  unfold efx_anchor_two_locks_preserve_three_ao; split_ifs <;> simp_all <;> omega

private lemma efx_anchor_two_locks_preserve_three_asum0 (r c : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r <= r+r+r) :
    (∑ x : Fin (r+r+r), (if efx_anchor_two_locks_preserve_three_ao r x = 0
      then c else 0)) = c * efx_anchor_two_locks_preserve_three_x0 r := by
  rw [show (∑ x : Fin (r+r+r),
        (if efx_anchor_two_locks_preserve_three_ao r x = 0 then c else 0))
      = ∑ x : Fin (r+r+r),
        (if x.val < efx_anchor_two_locks_preserve_three_x0 r then c else 0) from by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hh : efx_anchor_two_locks_preserve_three_ao r x = 0
    · rw [if_pos hh, if_pos ((efx_anchor_two_locks_preserve_three_ao0 r x).mp hh)]
    · rw [if_neg hh]
      by_cases h2 : x.val < efx_anchor_two_locks_preserve_three_x0 r
      · exact absurd ((efx_anchor_two_locks_preserve_three_ao0 r x).mpr h2) hh
      · rw [if_neg h2]]
  rw [efx_anchor_two_locks_preserve_three_sum_lt (r+r+r)
    (efx_anchor_two_locks_preserve_three_x0 r) c h, mul_comm]

private lemma efx_anchor_two_locks_preserve_three_asum1 (r c : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r <= r+r+r) :
    (∑ x : Fin (r+r+r), (if efx_anchor_two_locks_preserve_three_ao r x = 1
      then c else 0)) = c * efx_anchor_two_locks_preserve_three_x1 r := by
  rw [show (∑ x : Fin (r+r+r),
        (if efx_anchor_two_locks_preserve_three_ao r x = 1 then c else 0))
      = ∑ x : Fin (r+r+r),
        (if efx_anchor_two_locks_preserve_three_x0 r <= x.val ∧
          x.val < efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r then c else 0) from by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hh : efx_anchor_two_locks_preserve_three_ao r x = 1
    · rw [if_pos hh, if_pos ((efx_anchor_two_locks_preserve_three_ao1 r x).mp hh)]
    · rw [if_neg hh]
      by_cases h2 : efx_anchor_two_locks_preserve_three_x0 r <= x.val ∧
          x.val < efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r
      · exact absurd ((efx_anchor_two_locks_preserve_three_ao1 r x).mpr h2) hh
      · rw [if_neg h2]]
  rw [efx_anchor_two_locks_preserve_three_sum_between (r+r+r)
      (efx_anchor_two_locks_preserve_three_x0 r)
      (efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r) c h,
    show efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r
        - efx_anchor_two_locks_preserve_three_x0 r
      = efx_anchor_two_locks_preserve_three_x1 r by omega, mul_comm]

private lemma efx_anchor_two_locks_preserve_three_asum2 (r c : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r <= r+r+r) :
    (∑ x : Fin (r+r+r), (if efx_anchor_two_locks_preserve_three_ao r x = 2
      then c else 0)) = c * efx_anchor_two_locks_preserve_three_x2 r := by
  rw [show (∑ x : Fin (r+r+r),
        (if efx_anchor_two_locks_preserve_three_ao r x = 2 then c else 0))
      = ∑ x : Fin (r+r+r),
        (if efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r <= x.val ∧
          x.val < efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r
            + efx_anchor_two_locks_preserve_three_x2 r then c else 0) from by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hh : efx_anchor_two_locks_preserve_three_ao r x = 2
    · rw [if_pos hh, if_pos ((efx_anchor_two_locks_preserve_three_ao2 r x).mp hh)]
    · rw [if_neg hh]
      by_cases h2 : efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r <= x.val ∧
          x.val < efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r
            + efx_anchor_two_locks_preserve_three_x2 r
      · exact absurd ((efx_anchor_two_locks_preserve_three_ao2 r x).mpr h2) hh
      · rw [if_neg h2]]
  rw [efx_anchor_two_locks_preserve_three_sum_between (r+r+r)
      (efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r)
      (efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r
        + efx_anchor_two_locks_preserve_three_x2 r) c h,
    show efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r
        + efx_anchor_two_locks_preserve_three_x2 r
        - (efx_anchor_two_locks_preserve_three_x0 r
          + efx_anchor_two_locks_preserve_three_x1 r)
      = efx_anchor_two_locks_preserve_three_x2 r by omega, mul_comm]

private lemma efx_anchor_two_locks_preserve_three_asum3 (r c : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r <= r+r+r)
    (hsum : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r
      + efx_anchor_two_locks_preserve_three_x3 r = 3*r) :
    (∑ x : Fin (r+r+r), (if efx_anchor_two_locks_preserve_three_ao r x = 3
      then c else 0)) = c * efx_anchor_two_locks_preserve_three_x3 r := by
  rw [show (∑ x : Fin (r+r+r),
        (if efx_anchor_two_locks_preserve_three_ao r x = 3 then c else 0))
      = ∑ x : Fin (r+r+r),
        (if efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r
            + efx_anchor_two_locks_preserve_three_x2 r <= x.val then c else 0) from by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hh : efx_anchor_two_locks_preserve_three_ao r x = 3
    · rw [if_pos hh, if_pos ((efx_anchor_two_locks_preserve_three_ao3 r x).mp hh)]
    · rw [if_neg hh]
      by_cases h2 : efx_anchor_two_locks_preserve_three_x0 r
            + efx_anchor_two_locks_preserve_three_x1 r
            + efx_anchor_two_locks_preserve_three_x2 r <= x.val
      · exact absurd ((efx_anchor_two_locks_preserve_three_ao3 r x).mpr h2) hh
      · rw [if_neg h2]]
  rw [efx_anchor_two_locks_preserve_three_sum_ge (r+r+r)
      (efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r
        + efx_anchor_two_locks_preserve_three_x2 r) c h,
    show r + r + r - (efx_anchor_two_locks_preserve_three_x0 r
        + efx_anchor_two_locks_preserve_three_x1 r
        + efx_anchor_two_locks_preserve_three_x2 r)
      = efx_anchor_two_locks_preserve_three_x3 r by omega, mul_comm]

private lemma efx_anchor_two_locks_preserve_three_ossum (r : Nat) (i : Fin 4) :
    (∑ x : Fin 7,
      efx_anchor_family_values r 2 i (Fin.castAdd 2 (Fin.castAdd (r+r+r) x)))
      = efx_anchor_two_locks_preserve_three_os i := by
  simp only [efx_anchor_two_locks_preserve_three_old]
  fin_cases i <;> simp [efx_anchor_two_locks_preserve_three_os] <;> decide

private lemma efx_anchor_two_locks_preserve_three_lk2 (r : Nat) (i : Fin 4) :
    (∑ x : Fin 2, (if (if x.val = 0 then (2:Fin 4) else 3) = 2 then
      efx_anchor_family_values r 2 i (Fin.natAdd (7+(r+r+r)) x) else 0))
      = efx_anchor_two_locks_preserve_three_lv r i := by
  simp only [efx_anchor_two_locks_preserve_three_lock]
  rw [Fin.sum_univ_two]; simp

private lemma efx_anchor_two_locks_preserve_three_lk3 (r : Nat) (i : Fin 4) :
    (∑ x : Fin 2, (if (if x.val = 0 then (2:Fin 4) else 3) = 3 then
      efx_anchor_family_values r 2 i (Fin.natAdd (7+(r+r+r)) x) else 0))
      = efx_anchor_two_locks_preserve_three_lv r i := by
  simp only [efx_anchor_two_locks_preserve_three_lock]
  rw [Fin.sum_univ_two]; simp

private lemma efx_anchor_two_locks_preserve_three_bundle0 (r : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r <= r+r+r) (i : Fin 4) :
    (∑ h' ∈ bundle_of (efx_anchor_two_locks_preserve_three_sg r) 0,
      efx_anchor_family_values r 2 i h')
      = efx_anchor_two_locks_preserve_three_av i
        * efx_anchor_two_locks_preserve_three_x0 r := by
  rw [bundle_of, Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [efx_anchor_two_locks_preserve_three_sg, Fin.addCases_left,
    Fin.addCases_right, efx_anchor_two_locks_preserve_three_anchor]
  have hold : (∑ x : Fin 7, (if (3:Fin 4) = 0 then
      efx_anchor_family_values r 2 i (Fin.castAdd 2 (Fin.castAdd (r+r+r) x))
      else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp
  have hlock : (∑ x : Fin 2, (if (if x.val = 0 then (2:Fin 4) else 3) = 0 then
      efx_anchor_family_values r 2 i (Fin.natAdd (7+(r+r+r)) x) else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    by_cases hx : x.val = 0 <;> simp [hx]
  have hanch := efx_anchor_two_locks_preserve_three_asum0 r
    (efx_anchor_two_locks_preserve_three_av i) h
  rw [hold, hlock, Nat.zero_add, Nat.add_zero]
  exact hanch

private lemma efx_anchor_two_locks_preserve_three_bundle1 (r : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r <= r+r+r) (i : Fin 4) :
    (∑ h' ∈ bundle_of (efx_anchor_two_locks_preserve_three_sg r) 1,
      efx_anchor_family_values r 2 i h')
      = efx_anchor_two_locks_preserve_three_av i
        * efx_anchor_two_locks_preserve_three_x1 r := by
  rw [bundle_of, Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [efx_anchor_two_locks_preserve_three_sg, Fin.addCases_left,
    Fin.addCases_right, efx_anchor_two_locks_preserve_three_anchor]
  have hold : (∑ x : Fin 7, (if (3:Fin 4) = 1 then
      efx_anchor_family_values r 2 i (Fin.castAdd 2 (Fin.castAdd (r+r+r) x))
      else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp
  have hlock : (∑ x : Fin 2, (if (if x.val = 0 then (2:Fin 4) else 3) = 1 then
      efx_anchor_family_values r 2 i (Fin.natAdd (7+(r+r+r)) x) else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    by_cases hx : x.val = 0 <;> simp [hx]
  have hanch := efx_anchor_two_locks_preserve_three_asum1 r
    (efx_anchor_two_locks_preserve_three_av i) h
  rw [hold, hlock, Nat.zero_add, Nat.add_zero]
  exact hanch

private lemma efx_anchor_two_locks_preserve_three_bundle2 (r : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r <= r+r+r) (i : Fin 4) :
    (∑ h' ∈ bundle_of (efx_anchor_two_locks_preserve_three_sg r) 2,
      efx_anchor_family_values r 2 i h')
      = efx_anchor_two_locks_preserve_three_av i
        * efx_anchor_two_locks_preserve_three_x2 r
        + efx_anchor_two_locks_preserve_three_lv r i := by
  rw [bundle_of, Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [efx_anchor_two_locks_preserve_three_sg, Fin.addCases_left,
    Fin.addCases_right, efx_anchor_two_locks_preserve_three_anchor]
  have hold : (∑ x : Fin 7, (if (3:Fin 4) = 2 then
      efx_anchor_family_values r 2 i (Fin.castAdd 2 (Fin.castAdd (r+r+r) x))
      else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp
  have hlock := efx_anchor_two_locks_preserve_three_lk2 r i
  have hanch := efx_anchor_two_locks_preserve_three_asum2 r
    (efx_anchor_two_locks_preserve_three_av i) h
  rw [hold, hlock, Nat.zero_add]
  exact congrArg (fun t => t + efx_anchor_two_locks_preserve_three_lv r i) hanch

private lemma efx_anchor_two_locks_preserve_three_bundle3 (r : Nat)
    (h : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r <= r+r+r)
    (hsum : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r
      + efx_anchor_two_locks_preserve_three_x3 r = 3*r) (i : Fin 4) :
    (∑ h' ∈ bundle_of (efx_anchor_two_locks_preserve_three_sg r) 3,
      efx_anchor_family_values r 2 i h')
      = efx_anchor_two_locks_preserve_three_os i
        + efx_anchor_two_locks_preserve_three_av i
          * efx_anchor_two_locks_preserve_three_x3 r
        + efx_anchor_two_locks_preserve_three_lv r i := by
  rw [bundle_of, Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [efx_anchor_two_locks_preserve_three_sg, Fin.addCases_left,
    Fin.addCases_right, efx_anchor_two_locks_preserve_three_anchor, if_true]
  have hold := efx_anchor_two_locks_preserve_three_ossum r i
  have hlock := efx_anchor_two_locks_preserve_three_lk3 r i
  have hanch := efx_anchor_two_locks_preserve_three_asum3 r
    (efx_anchor_two_locks_preserve_three_av i) h hsum
  rw [hold, hlock]
  exact congrArg (fun t => (efx_anchor_two_locks_preserve_three_os i + t)
    + efx_anchor_two_locks_preserve_three_lv r i) hanch

private lemma efx_anchor_two_locks_preserve_three_bundle_sum (r : Nat) (hr : 3 <= r)
    (i j : Fin 4) :
    (∑ h' ∈ bundle_of (efx_anchor_two_locks_preserve_three_sg r) j,
      efx_anchor_family_values r 2 i h')
      = efx_anchor_two_locks_preserve_three_bv r i j := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩ :=
    efx_anchor_two_locks_preserve_three_arith r hr
  have hd4 : 4 * ((r-3)/4) + (r-3)%4 = r - 3 := Nat.div_add_mod (r-3) 4
  have hd4' : (r - 3) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hsum : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r
      + efx_anchor_two_locks_preserve_three_x3 r = 3*r := by
    simp only [efx_anchor_two_locks_preserve_three_x0,
      efx_anchor_two_locks_preserve_three_x1,
      efx_anchor_two_locks_preserve_three_x2,
      efx_anchor_two_locks_preserve_three_x3]
    split_ifs <;> omega
  have hN : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r
      + efx_anchor_two_locks_preserve_three_x2 r <= r+r+r := by omega
  have h1 : efx_anchor_two_locks_preserve_three_x0 r <= r+r+r := by omega
  have h2' : efx_anchor_two_locks_preserve_three_x0 r
      + efx_anchor_two_locks_preserve_three_x1 r <= r+r+r := by omega
  fin_cases j
  · simpa [efx_anchor_two_locks_preserve_three_bv]
      using efx_anchor_two_locks_preserve_three_bundle0 r h1 i
  · simpa [efx_anchor_two_locks_preserve_three_bv]
      using efx_anchor_two_locks_preserve_three_bundle1 r h2' i
  · simpa [efx_anchor_two_locks_preserve_three_bv]
      using efx_anchor_two_locks_preserve_three_bundle2 r hN i
  · simpa [efx_anchor_two_locks_preserve_three_bv]
      using efx_anchor_two_locks_preserve_three_bundle3 r hN hsum i

theorem efx_anchor_two_locks_preserve_three (r : ℕ) (hr : 0 < r) :
  ∃ σ : Fin ((7+(r+r+r))+2) → Fin 4,
    is_efx_goods (fun i g => (efx_anchor_family_values r 2 i g : ℝ)) σ ∧
    (∀ i : Fin 3, (efx_anchor_family_baseline r 2 i.castSucc : ℝ) ≤
      additive_valuation (fun g => (efx_anchor_family_values r 2 i.castSucc g : ℝ))
        (bundle_of σ i.castSucc)) := by
  rcases Nat.lt_or_ge r 3 with hlt | h3
  · interval_cases r
    · refine ⟨![(1 : Fin 4), 3, 1, 3, 1, 2, 3, 0, 0, 1, 2, 3], ?_, ?_⟩
      · rw [is_efx_goods_nat_cast_iff]; decide
      · intro i
        rw [efx_anchor_two_locks_preserve_three_real_le_iff]
        revert i
        decide
    · refine ⟨![(3 : Fin 4), 3, 3, 3, 2, 2, 3, 0, 0, 0, 1, 1, 1, 2, 3], ?_, ?_⟩
      · rw [is_efx_goods_nat_cast_iff]; decide
      · intro i
        rw [efx_anchor_two_locks_preserve_three_real_le_iff]
        revert i
        decide
  · refine ⟨efx_anchor_two_locks_preserve_three_sg r, ?_, ?_⟩
    · rw [is_efx_goods_nat_cast_iff]
      intro i j hij g hg
      simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      rw [efx_anchor_two_locks_preserve_three_bundle_sum r h3 i j,
        efx_anchor_two_locks_preserve_three_bundle_sum r h3 i i]
      have h1 : efx_anchor_two_locks_preserve_three_lbv i j
          <= efx_anchor_family_values r 2 i g := by
        rw [← hg]
        exact efx_anchor_two_locks_preserve_three_lb_le r (by omega) i g
      have h2 := efx_anchor_two_locks_preserve_three_bv_efx r h3 i j hij
      omega
    · intro i
      rw [efx_anchor_two_locks_preserve_three_real_le_iff]
      rw [efx_anchor_two_locks_preserve_three_bundle_sum r h3 i.castSucc i.castSucc]
      exact efx_anchor_two_locks_preserve_three_bv_ir r h3 i
