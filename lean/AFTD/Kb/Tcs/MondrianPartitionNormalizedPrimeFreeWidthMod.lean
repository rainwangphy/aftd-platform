import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianListSumCountMod
import AFTD.Kb.Tcs.MondrianPartitionFloorMomentDivWidth
import AFTD.Kb.Tcs.MondrianRectFloorContribution
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_partition_normalized_prime_free_width_mod

Topic: combinatorics   Node: 284d61500436

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_min_width_layer_count, from the normalized floor moment for arXiv:2610.19193, Section 1.

In an admissible n-square partition with every width divisible by positive d and with constant normalized area C, the number of normalized widths indivisible by prime p, multiplied by the p-free part of C, is congruent modulo p to (n/d) times floor(n/p^v_p(C)).
-/

theorem mondrian_partition_normalized_prime_free_width_mod (n p d C : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hp : Nat.Prime p) (hd : 0 < d) (hP : mondrian_is_partition n P)
    (hwidth : ∀ r ∈ P, d ∣ mondrian_rect_width r)
    (harea : ∀ r ∈ P, (mondrian_rect_width r / d) * mondrian_rect_height r = C) :
    Nat.ModEq p
      ((P.countP (fun r => decide (¬ p ∣ mondrian_rect_width r / d))) *
        (C / p ^ C.factorization p))
      ((n / d) * (n / p ^ C.factorization p)) := by
  let q := p ^ C.factorization p
  let u := C / q
  let f := fun r : ℕ × ℕ × ℕ × ℕ => ((mondrian_rect_width r / d : ℕ) : ℤ) *
    (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ))
  let pred := fun r : ℕ × ℕ × ℕ × ℕ => decide (¬ p ∣ mondrian_rect_width r / d)
  have hq : 0 < q := pow_pos hp.pos _
  have hterm : ∀ r ∈ P, (p : ℤ) ∣ f r - if pred r then (u : ℤ) else 0 := by
    intro r hr
    by_cases hw : p ∣ mondrian_rect_width r / d
    · have hwZ : (p : ℤ) ∣ ((mondrian_rect_width r / d : ℕ) : ℤ) := by exact_mod_cast hw
      simpa only [f, pred, hw, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, sub_zero] using dvd_mul_of_dvd_left hwZ
          ((((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ)))
    · have hcop : q.Coprime (mondrian_rect_width r / d) :=
        (hp.coprime_iff_not_dvd.mpr hw).pow_left _
      have hqh : q ∣ mondrian_rect_height r := by
        apply hcop.dvd_mul_left.mp
        rw [harea r hr]
        exact Nat.ordProj_dvd C p
      let v : ℕ × ℕ × ℕ × ℕ := (0, mondrian_rect_width r / d, r.2.2.1, r.2.2.2)
      have he := mondrian_rect_floor_contribution v
        (Nat.le_of_lt (hP.2.1 r hr).2) q hq hqh
      change ((mondrian_rect_width r / d : ℕ) : ℤ) *
        (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ)) =
          (((mondrian_rect_width r / d) * mondrian_rect_height r / q : ℕ) : ℤ) at he
      rw [harea r hr] at he
      simp only [f, pred, hw, not_false_eq_true, decide_true, if_true]
      change (p : ℤ) ∣ _ - (C / q : ℕ)
      rw [he]
      simp
  have hsum := mondrian_list_sum_count_mod P (p : ℤ) (u : ℤ) f pred hterm
  have hmoment := mondrian_partition_floor_moment_div_width n q d P hd hP hwidth
  change (P.map f).sum = ((n / d : ℕ) : ℤ) * ((n / q : ℕ) : ℤ) at hmoment
  rw [hmoment] at hsum
  exact Nat.modEq_iff_dvd.mpr (by exact_mod_cast hsum)
