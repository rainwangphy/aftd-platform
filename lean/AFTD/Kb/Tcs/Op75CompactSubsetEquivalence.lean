import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Run
import AFTD.Kb.Tcs.Op75Subset
import AFTD.Kb.Tcs.Op75CompactMap
import AFTD.Kb.Tcs.Op75CompactDigit

/-!
# op75_compact_subset_equivalence

Topic: np_completeness   Node: 6b0901d4c04c

Provenance: helper lemma. OP-75, arXiv:2610.06092, one-pass subset-sum construction; a helper toward interval verification.

For any list of real weights and real target, the compact-map orbit ends at zero with accumulated digit-weighted sum equal to the target for some input in the unit interval if and only if the target is a subset sum of the list.
-/

open Set

lemma op75_run_one (F E : ℝ → ℝ) (h1 : F 1 = 1) (as : List ℝ) :
    (op75_run F E as 1).1 = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [op75_run, h1] using ih

theorem op75_subset_orbit (F E : ℝ → ℝ)
    (hclosed : ∀ x ∈ Icc (0:ℝ) 1, F x ∈ Icc (0:ℝ) 1)
    (h1 : F 1 = 1)
    (hbool : ∀ x ∈ Icc (0:ℝ) 1, F x ≠ 1 → E x = 0 ∨ E x = 1)
    (hpre0 : ∀ y ∈ Icc (0:ℝ) 1, ∃ x ∈ Icc (0:ℝ) 1, F x = y ∧ E x = 0)
    (hpre1 : ∀ y ∈ Icc (0:ℝ) 1, ∃ x ∈ Icc (0:ℝ) 1, F x = y ∧ E x = 1)
    (as : List ℝ) (t : ℝ) :
    (∃ x ∈ Icc (0:ℝ) 1, (op75_run F E as x).1 = 0 ∧ (op75_run F E as x).2 = t) ↔ op75_subset as t := by
  induction as generalizing t with
  | nil =>
      constructor
      · rintro ⟨x, hx, he, hs⟩
        simpa [op75_run, op75_subset] using hs.symm
      · intro ht
        have ht' : t = 0 := by simpa [op75_subset] using ht
        subst t
        exact ⟨0, by norm_num, rfl, rfl⟩
  | cons a as ih =>
      constructor
      · rintro ⟨x, hx, he, hs⟩
        have hne : F x ≠ 1 := by
          intro heq
          have hzero : (op75_run F E as 1).1 = 0 := by simpa [op75_run, heq] using he
          rw [op75_run_one F E h1 as] at hzero
          norm_num at hzero
        have htail : op75_subset as (op75_run F E as (F x)).2 := by
          apply (ih _).mp
          exact ⟨F x, hclosed x hx, by simpa [op75_run] using he, rfl⟩
        have hsum : a * E x + (op75_run F E as (F x)).2 = t := by simpa [op75_run] using hs
        rcases hbool x hx hne with hE | hE
        · left
          rw [hE] at hsum
          have : (op75_run F E as (F x)).2 = t := by linarith
          simpa [this] using htail
        · right
          rw [hE] at hsum
          have : (op75_run F E as (F x)).2 = t-a := by linarith
          simpa [this] using htail
      · intro ht
        rcases ht with ht | ht
        · obtain ⟨y, hy, hy0, hys⟩ := (ih t).mpr ht
          obtain ⟨x, hx, hfx, he0⟩ := hpre0 y hy
          refine ⟨x, hx, ?_, ?_⟩
          · simpa [op75_run, hfx] using hy0
          · simpa [op75_run, hfx, he0] using hys
        · obtain ⟨y, hy, hy0, hys⟩ := (ih (t-a)).mpr ht
          obtain ⟨x, hx, hfx, he1⟩ := hpre1 y hy
          refine ⟨x, hx, ?_, ?_⟩
          · simpa [op75_run, hfx] using hy0
          · simp only [op75_run, hfx, he1, mul_one]
            linarith

lemma op75_compact_closed (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    op75_compact_map x ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact le_min (by norm_num) (le_min (by linarith [hx.1]) (abs_nonneg _))
  · exact min_le_left _ _

lemma op75_compact_one : op75_compact_map 1 = 1 := by
  norm_num [op75_compact_map]

lemma op75_compact_digit_low (x : ℝ) (hx : x ≤ 1/4) : op75_compact_digit x = 0 := by
  unfold op75_compact_digit
  apply max_eq_left
  exact le_trans (min_le_right _ _) (by linarith)

lemma op75_compact_digit_high (x : ℝ) (hx : 1/2 ≤ x) : op75_compact_digit x = 1 := by
  unfold op75_compact_digit
  rw [min_eq_left (by linarith : (1:ℝ) ≤ 4*x-1)]
  norm_num

lemma op75_compact_boolean (x : ℝ) (_hx : x ∈ Icc (0:ℝ) 1)
    (hne : op75_compact_map x ≠ 1) : op75_compact_digit x = 0 ∨ op75_compact_digit x = 1 := by
  by_cases hlo : x ≤ 1/4
  · exact Or.inl (op75_compact_digit_low x hlo)
  by_cases hhi : 1/2 ≤ x
  · exact Or.inr (op75_compact_digit_high x hhi)
  exfalso
  apply hne
  have ha : (1:ℝ) ≤ 4*x := by linarith
  have hb : (1:ℝ) ≤ |4*x-3| := by
    have h := neg_le_abs (4*x-3)
    linarith
  exact min_eq_left (le_min ha hb)

lemma op75_compact_pre0 (y : ℝ) (hy : y ∈ Icc (0:ℝ) 1) :
    ∃ x ∈ Icc (0:ℝ) 1, op75_compact_map x = y ∧ op75_compact_digit x = 0 := by
  let x : ℝ := y/4
  have hx0 : 0 ≤ x := by dsimp [x]; linarith [hy.1]
  have hx1 : x ≤ 1 := by dsimp [x]; linarith [hy.2]
  have hxb : 4*x-3 ≤ 0 := by dsimp [x]; linarith [hy.2]
  have hsel : op75_compact_digit x = 0 := op75_compact_digit_low x (by dsimp [x]; linarith [hy.2])
  have hfx : op75_compact_map x = y := by
    unfold op75_compact_map
    rw [abs_of_nonpos hxb]
    have hsmall : 4*x ≤ -(4*x-3) := by dsimp [x]; linarith [hy.2]
    rw [min_eq_left hsmall, min_eq_right (by dsimp [x]; linarith [hy.2])]
    dsimp [x]
    ring
  exact ⟨x, ⟨hx0,hx1⟩, hfx, hsel⟩

lemma op75_compact_pre1 (y : ℝ) (hy : y ∈ Icc (0:ℝ) 1) :
    ∃ x ∈ Icc (0:ℝ) 1, op75_compact_map x = y ∧ op75_compact_digit x = 1 := by
  let x : ℝ := (y+3)/4
  have hx0 : 0 ≤ x := by dsimp [x]; linarith [hy.1]
  have hx1 : x ≤ 1 := by dsimp [x]; linarith [hy.2]
  have hxb : 0 ≤ 4*x-3 := by dsimp [x]; linarith [hy.1]
  have hsel : op75_compact_digit x = 1 := op75_compact_digit_high x (by dsimp [x]; linarith [hy.1])
  have hfx : op75_compact_map x = y := by
    unfold op75_compact_map
    rw [abs_of_nonneg hxb]
    have hsmall : 4*x-3 ≤ 4*x := by linarith
    rw [min_eq_right hsmall, min_eq_right (by dsimp [x]; linarith [hy.2])]
    dsimp [x]
    ring
  exact ⟨x, ⟨hx0,hx1⟩, hfx, hsel⟩

theorem op75_compact_subset_equivalence (as : List ℝ) (t : ℝ) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, (op75_run op75_compact_map op75_compact_digit as x).1 = 0 ∧
       (op75_run op75_compact_map op75_compact_digit as x).2 = t) ↔ op75_subset as t := by
  exact op75_subset_orbit op75_compact_map op75_compact_digit op75_compact_closed op75_compact_one
    op75_compact_boolean op75_compact_pre0 op75_compact_pre1 as t
