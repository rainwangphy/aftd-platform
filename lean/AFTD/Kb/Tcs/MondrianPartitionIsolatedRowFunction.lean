import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianListSumCountMod
import AFTD.Kb.Tcs.MondrianPartitionHorizontalMoment
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectHeight

/-!
# mondrian_partition_isolated_row_function

Topic: combinatorics   Node: 88dd1982b67e

Provenance: helper lemma. Helper for OP-280, arXiv:2610.19193, Section 1. Height-level networks are motivated by the graph model in arXiv:2007.09639, Section 1; the filtered graph and row-potential cut argument are developed here for the remaining cases with at least three prime factors.

Let d divide the square side. If an integer row-level function has increment one on a selected tile and has zero increment on every other tile whose width is indivisible by d, then the selected width is divisible by d.
-/

theorem mondrian_partition_isolated_row_function (n d : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hdn : d ∣ n)
    (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) (f : ℕ → ℤ)
    (hrstep : f r.2.2.2 - f r.2.2.1 = 1)
    (hothers : ∀ s ∈ P, s ≠ r → d ∣ mondrian_rect_width s ∨ f s.2.2.2 = f s.2.2.1) :
    d ∣ mondrian_rect_width r := by
  let g := fun s : ℕ × ℕ × ℕ × ℕ =>
    (mondrian_rect_width s : ℤ) * (f s.2.2.2 - f s.2.2.1)
  have hgr : g r = (mondrian_rect_width r : ℤ) := by dsimp [g]; rw [hrstep]; ring
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
      · simp [g, hh]
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
