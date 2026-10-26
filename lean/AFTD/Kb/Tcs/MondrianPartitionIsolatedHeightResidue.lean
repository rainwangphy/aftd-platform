import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianListSumCountMod
import AFTD.Kb.Tcs.MondrianPartitionHorizontalMoment
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_partition_isolated_height_residue

Topic: combinatorics   Node: a886add3efa1

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

Let d divide the square side. If every tile except r either has width divisible by d or height divisible by m, and r has height indivisible by m, then the width of r is divisible by d.
-/

theorem mondrian_partition_isolated_height_residue (n d m : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hdn : d ∣ n)
    (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P)
    (hrm : ¬ m ∣ mondrian_rect_height r)
    (hothers : ∀ s ∈ P, s ≠ r → d ∣ mondrian_rect_width s ∨ m ∣ mondrian_rect_height s) :
    d ∣ mondrian_rect_width r := by
  let f : ℕ → ℤ := fun y => if y % m = r.2.2.2 % m then 1 else 0
  let g := fun s : ℕ × ℕ × ℕ × ℕ =>
    (mondrian_rect_width s : ℤ) * (f s.2.2.2 - f s.2.2.1)
  have hrmod : r.2.2.1 % m ≠ r.2.2.2 % m := by
    intro hh
    apply hrm
    exact (Nat.modEq_iff_dvd' (Nat.le_of_lt (hP.2.1 r hr).2)).mp hh
  have hgr : g r = (mondrian_rect_width r : ℤ) := by simp [g, f, hrmod]
  have hterm : ∀ s ∈ P, (d : ℤ) ∣ g s - if s == r then (mondrian_rect_width r : ℤ) else 0 := by
    intro s hs
    by_cases he : s = r
    · subst s
      simp [hgr]
    · have hfalse : (s == r) = false := by simp [he]
      simp only [hfalse, Bool.false_eq_true, if_false, sub_zero]
      rcases hothers s hs he with hw | hh
      · have hwZ : (d : ℤ) ∣ (mondrian_rect_width s : ℤ) := by exact_mod_cast hw
        exact dvd_mul_of_dvd_left hwZ _
      · have hmod : s.2.2.1 % m = s.2.2.2 % m :=
          (Nat.modEq_iff_dvd' (Nat.le_of_lt (hP.2.1 s hs).2)).mpr hh
        simp [g, f, hmod]
  have hnodup : P.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    apply hP.2.2.1.imp
    intro a b hab he
    subst b
    exact hab.2 (Or.inl ⟨rfl, rfl⟩)
  have hcount : P.countP (fun s => s == r) = 1 := by
    simpa only [← List.count_eq_countP] using List.count_eq_one_of_mem hnodup hr
  have hsum := mondrian_list_sum_count_mod P (d : ℤ) (mondrian_rect_width r : ℤ)
    g (fun s => s == r) hterm
  rw [hcount] at hsum
  simp only [Nat.cast_one, one_mul] at hsum
  have htotal : (d : ℤ) ∣ (P.map g).sum := by
    rw [show (P.map g).sum = (n : ℤ) * (f n - f 0) from
      mondrian_partition_horizontal_moment n P hP f]
    exact dvd_mul_of_dvd_left (by exact_mod_cast hdn) _
  have hh := dvd_sub htotal hsum
  have heq : (P.map g).sum - ((P.map g).sum - (mondrian_rect_width r : ℤ)) =
      (mondrian_rect_width r : ℤ) := by ring
  rw [heq] at hh
  exact_mod_cast hh
