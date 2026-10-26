import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPartitionHorizontalMoment
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_partition_row_width_sum

Topic: combinatorics   Node: ec1ca2258c68

Provenance: helper lemma. Helper for OP-280. Cross-section identity underlying HAL:hal-05729522v2, Lemma 2.3; also follows from the horizontal moment.

At every integer row y below n in an admissible n-square partition, the widths of the tiles crossing that row sum to n.
-/

/-- A sum of `if p then g else 0` over a list equals the sum of `g` over the filtered list. -/
private lemma mondrian_partition_row_width_sum_sum_map_ite {α : Type} (l : List α)
    (p : α → Prop) [DecidablePred p] (g : α → ℤ) :
    (l.map (fun r => if p r then g r else 0)).sum = ((l.filter (fun r => decide (p r))).map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

/-- Casting a list sum of widths to integers equals the list sum of the cast widths. -/
private lemma mondrian_partition_row_width_sum_cast_sum (l : List (ℕ × ℕ × ℕ × ℕ)) :
    ((l.map (fun r => (mondrian_rect_width r : ℤ))).sum)
      = (((l.map mondrian_rect_width).sum : ℕ) : ℤ) := by
  change ((List.map (Nat.cast ∘ mondrian_rect_width) l).sum) = _
  rw [← List.map_map, ← Nat.cast_list_sum]

theorem mondrian_partition_row_width_sum (n y : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P) (hy : y < n) :
    ((P.filter (fun r => decide (r.2.2.1 ≤ y ∧ y < r.2.2.2))).map mondrian_rect_width).sum = n := by
  let f : ℕ → ℤ := fun t => if y < t then 1 else 0
  have hm := mondrian_partition_horizontal_moment n P hP f
  have hstep : ∀ r ∈ P, (mondrian_rect_width r : ℤ) * (f r.2.2.2 - f r.2.2.1)
      = (if (r.2.2.1 ≤ y ∧ y < r.2.2.2) then (mondrian_rect_width r : ℤ) else 0) := by
    intro r hr
    have hbt := (hP.2.1 r hr).2
    simp only [f]
    by_cases htop : y < r.2.2.2
    · by_cases hbot : y < r.2.2.1
      · simp [htop, hbot]
      · have hc : (r.2.2.1 ≤ y ∧ y < r.2.2.2) := ⟨by omega, htop⟩
        simp [htop, hbot, hc]
    · have hbot : ¬ y < r.2.2.1 := by omega
      simp [htop, hbot]
  have hmap : P.map (fun r => (mondrian_rect_width r : ℤ) * (f r.2.2.2 - f r.2.2.1))
      = P.map (fun r => if (r.2.2.1 ≤ y ∧ y < r.2.2.2) then (mondrian_rect_width r : ℤ) else 0) :=
    List.map_congr_left hstep
  have hfilter : (P.map (fun r => if (r.2.2.1 ≤ y ∧ y < r.2.2.2) then (mondrian_rect_width r : ℤ) else 0)).sum
      = ((P.filter (fun r => decide (r.2.2.1 ≤ y ∧ y < r.2.2.2))).map (fun r => (mondrian_rect_width r : ℤ))).sum :=
    mondrian_partition_row_width_sum_sum_map_ite P _ _
  have hnat := mondrian_partition_row_width_sum_cast_sum
    (P.filter (fun r => decide (r.2.2.1 ≤ y ∧ y < r.2.2.2)))
  have hfn : f n - f 0 = 1 := by
    simp only [f]
    rw [if_pos hy]
    have h0 : ¬ (y < 0) := by omega
    rw [if_neg h0]
    norm_num
  have h2 : ((((P.filter (fun r => decide (r.2.2.1 ≤ y ∧ y < r.2.2.2))).map mondrian_rect_width).sum : ℕ) : ℤ) = (n : ℤ) := by
    rw [← hnat, ← hfilter, ← hmap, hm, hfn, mul_one]
  exact_mod_cast h2
