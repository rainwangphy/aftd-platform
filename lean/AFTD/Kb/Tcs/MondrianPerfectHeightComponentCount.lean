import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianHeightGraph
import AFTD.Kb.Tcs.MondrianHeightGraphAdjOfMem
import AFTD.Kb.Tcs.MondrianPartitionHorizontalMoment
import AFTD.Kb.Tcs.MondrianRectFloorContribution
import AFTD.Kb.Tcs.MondrianListSumCountMod
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# mondrian_perfect_height_component_count

Topic: combinatorics   Node: 583fa28c8378

Provenance: helper lemma. Helper for OP-280 and the width-indivisible height graph; componentwise refinement of the prime-free side-count congruence.

For a perfect admissible n-square partition and prime p dividing n, each connected component of the height graph contains a number of width-indivisible tiles divisible by p. The decidability parameter merely supplies a classical component-membership test.
-/

theorem mondrian_perfect_height_component_count (n p a : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ))
    [DecidablePred ((mondrian_height_graph p P).Reachable a)]
    (hp : Nat.Prime p) (hpn : p ∣ n) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0) :
    p ∣ P.countP (fun r => decide (¬ p ∣ mondrian_rect_width r ∧
      (mondrian_height_graph p P).Reachable a r.2.2.1)) := by
  classical
  have hlen : 0 < P.length := Nat.lt_of_lt_of_le (by decide) hP.1
  have hne : P ≠ [] := List.ne_nil_of_length_pos hlen
  obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil P hne
  have hApos : 0 < mondrian_rect_area r0 := by
    obtain ⟨-, -, hw, hh, -⟩ := mondrian_partition_bounds n P hP r0 hr0
    exact Nat.mul_pos hw hh
  let q := p ^ (mondrian_rect_area r0).factorization p
  let u := mondrian_rect_area r0 / q
  let H := mondrian_height_graph p P
  let f : ℕ → ℤ := fun y => if H.Reachable a y then ((y / q : ℕ) : ℤ) else 0
  let pred : (ℕ × ℕ × ℕ × ℕ) → Bool := fun r =>
    decide (¬ p ∣ mondrian_rect_width r ∧ H.Reachable a r.2.2.1)
  let F : (ℕ × ℕ × ℕ × ℕ) → ℤ := fun r =>
    (mondrian_rect_width r : ℤ) * (f r.2.2.2 - f r.2.2.1)
  have hq : 0 < q := pow_pos hp.pos _
  have hterm : ∀ r ∈ P, (p : ℤ) ∣ F r - if pred r then (u : ℤ) else 0 := by
    intro r hr
    have hAr : mondrian_rect_area r = mondrian_rect_area r0 :=
      mondrian_defect_zero_equal P hz r r0 hr hr0
    by_cases hw : p ∣ mondrian_rect_width r
    · have hwZ : (p : ℤ) ∣ (mondrian_rect_width r : ℤ) := by exact_mod_cast hw
      have hpred : pred r = false := by
        simp only [pred]
        apply decide_eq_false
        intro h
        exact h.1 hw
      simp only [F, hpred, Bool.false_eq_true, if_false, sub_zero]
      exact dvd_mul_of_dvd_left hwZ _
    · have hcop : q.Coprime (mondrian_rect_width r) :=
        (hp.coprime_iff_not_dvd.mpr hw).pow_left _
      have hqh : q ∣ mondrian_rect_height r := by
        apply hcop.dvd_mul_left.mp
        change q ∣ mondrian_rect_area r
        rw [hAr]
        exact Nat.ordProj_dvd _ p
      have he := mondrian_rect_floor_contribution r
        (Nat.le_of_lt (hP.2.1 r hr).2) q hq hqh
      rw [hAr] at he
      have hadj : H.Adj r.2.2.1 r.2.2.2 :=
        mondrian_height_graph_adj_of_mem p P r hr hw (hP.2.1 r hr).2
      have hreach_iff : H.Reachable a r.2.2.2 ↔ H.Reachable a r.2.2.1 :=
        ⟨fun h => h.trans hadj.reachable.symm, fun h => h.trans hadj.reachable⟩
      have hFeq : F r = if pred r then (u : ℤ) else 0 := by
        by_cases hrb : H.Reachable a r.2.2.1
        · have hrt : H.Reachable a r.2.2.2 := hreach_iff.mpr hrb
          have hpred : pred r = true := by simp [pred, hw, hrb]
          simp only [F, f, hrb, hrt, hpred, if_true]
          rw [he]
        · have hrt : ¬ H.Reachable a r.2.2.2 := fun h => hrb (hreach_iff.mp h)
          have hpred : pred r = false := by
            simp only [pred]
            apply decide_eq_false
            intro h; exact hrb h.2
          simp only [F, f, hrb, hrt, hpred, Bool.false_eq_true, if_false]
          ring
      rw [hFeq]
      simp
  have hsum := mondrian_list_sum_count_mod P (p : ℤ) (u : ℤ) F pred hterm
  have hmoment := mondrian_partition_horizontal_moment n P hP f
  have hnZ : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
  have hsumdiv : (p : ℤ) ∣ (P.map F).sum := by
    rw [show (P.map F).sum = (n : ℤ) * (f n - f 0) from hmoment]
    exact dvd_mul_of_dvd_left hnZ _
  have hprod : (p : ℤ) ∣ (P.countP pred : ℤ) * (u : ℤ) := by
    have hh := dvd_sub hsumdiv hsum
    have heq : (P.map F).sum - ((P.map F).sum - (P.countP pred : ℤ) * (u : ℤ)) =
        (P.countP pred : ℤ) * (u : ℤ) := by ring
    rwa [heq] at hh
  have hprodN : p ∣ P.countP pred * u := by exact_mod_cast hprod
  rcases hp.dvd_mul.mp hprodN with hc | hu
  · exact hc
  · exact (Nat.not_dvd_ordCompl hp (Nat.ne_of_gt hApos) hu).elim
