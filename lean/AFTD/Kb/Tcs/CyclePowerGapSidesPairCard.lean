import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide
import AFTD.Kb.Tcs.BoolSumEqCardFilter

/-!
# cycle_power_gap_sides_pair_card

Topic: combinatorics   Node: d16e9b5e758c

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

For a profile rooted below g at most D, whose selected distance D-R pairs cross the two blocks, its pair count equals the number of compressed side pairs at forward distance R.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_gap_sides_pair_card
    (D R g r : ℕ) (hRD : R ≤ D) (hg : g ≤ D) (hr : r < g) (b : ℕ → Bool)
    (hcross : ∀ a < R, b a = true → b (a+D-R) = true →
      r+a < g ∧ D ≤ r+(a+D-R)) :
    (range R).sum (fun a => (b a && b (a+D-R)).toNat) =
      (((cycle_power_gap_left_side g r b).product (cycle_power_gap_right_side D g r b)).filter
        (fun p : Fin g × Fin g => p.2.val+R = p.1.val)).card := by
  classical
  rw [bool_sum_eq_card_filter]
  let S := (range R).filter (fun a => (b a && b (a+D-R)) = true)
  let f (a : ℕ) (ha : a ∈ S) : Fin g × Fin g :=
    (⟨r+a, by
      have hb := (mem_filter.mp ha).2
      have hbb : b a = true ∧ b (a+D-R) = true := by simpa only [Bool.and_eq_true] using hb
      exact (hcross a (mem_range.mp (mem_filter.mp ha).1) hbb.1 hbb.2).1⟩,
     ⟨r+a-R, by
      have hb := (mem_filter.mp ha).2
      have hbb : b a = true ∧ b (a+D-R) = true := by simpa only [Bool.and_eq_true] using hb
      have hc := hcross a (mem_range.mp (mem_filter.mp ha).1) hbb.1 hbb.2
      omega⟩)
  change S.card = _
  apply card_bij f
  · intro a ha
    have haR := mem_range.mp (mem_filter.mp ha).1
    have hb := (mem_filter.mp ha).2
    have hbb : b a = true ∧ b (a+D-R) = true := by simpa only [Bool.and_eq_true] using hb
    have hc := hcross a haR hbb.1 hbb.2
    apply mem_filter.mpr
    constructor
    · apply mem_product.mpr
      constructor
      · apply mem_filter.mpr
        refine ⟨mem_univ _, by dsimp [f]; omega, ?_⟩
        have he : (f a ha).1.val-r = a := by dsimp [f]; omega
        simpa only [he] using hbb.1
      · apply mem_filter.mpr
        refine ⟨mem_univ _, by dsimp [f]; omega, ?_⟩
        have he : D+(f a ha).2.val-r = a+D-R := by dsimp [f]; omega
        simpa only [he] using hbb.2
    · dsimp [f]
      omega
  · intro a ha a' ha' he
    have heval := congrArg (fun p : Fin g × Fin g => p.1.val) he
    dsimp [f] at heval
    omega
  · intro p hp
    have hdist := (mem_filter.mp hp).2
    have hparts := mem_product.mp (mem_filter.mp hp).1
    have hri := (mem_filter.mp hparts.1).2.1
    have hbi := (mem_filter.mp hparts.1).2.2
    have hjr := (mem_filter.mp hparts.2).2.1
    have hbj := (mem_filter.mp hparts.2).2.2
    have haR : p.1.val-r < R := by omega
    have haoff : (p.1.val-r)+D-R = D+p.2.val-r := by omega
    have ha : p.1.val-r ∈ S := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr haR, ?_⟩
      simp only [Bool.and_eq_true, haoff]
      exact ⟨hbi, hbj⟩
    refine ⟨p.1.val-r, ha, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;> dsimp [f] <;> omega
