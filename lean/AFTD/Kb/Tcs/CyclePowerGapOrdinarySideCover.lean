import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide

/-!
# cycle_power_gap_ordinary_side_cover

Topic: combinatorics   Node: aa954e5dd2be

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Ordinary distance coverage in an integer radius-D model, restricted to g at most D, gives a cut-separated biclique cover of the complete ordered graph on Fin g.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_gap_ordinary_side_cover
    (D g : ℕ) (hg : g ≤ D) (x : ℤ → ℕ → Bool)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < D → ∀ v : ℤ,
      ∃ a : ℕ, a < D-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true) :
    ∀ i j : Fin g, i < j → ∃ r : Fin (g-1),
      i ∈ cycle_power_gap_right_side D g (r.val+1) (x ((r.val+1 : ℕ) : ℤ)) ∧
      j ∈ cycle_power_gap_left_side g (r.val+1) (x ((r.val+1 : ℕ) : ℤ)) := by
  intro i j hij
  have hi : i.val < g := i.isLt
  have hj : j.val < g := j.isLt
  have hij' : i.val < j.val := hij
  let d := D-(j.val-i.val)
  have hd₀ : 1 ≤ d := by dsimp [d]; omega
  have hdD : d < D := by dsimp [d]; omega
  obtain ⟨a, ha, h₀, h₁⟩ := hcover d hd₀ hdD (j.val : ℤ)
  have ha' : a < j.val-i.val := by dsimp [d] at ha; omega
  let r : Fin (g-1) := ⟨j.val-a-1, by omega⟩
  have hr : r.val+1 = j.val-a := by dsimp [r]; omega
  have hroot : (j.val : ℤ)-(a : ℤ) = ((r.val+1 : ℕ) : ℤ) := by omega
  have ha₀ : j.val-(r.val+1) = a := by omega
  have ha₁ : D+i.val-(r.val+1) = a+d := by dsimp [d]; omega
  refine ⟨r, ?_, ?_⟩
  · apply mem_filter.mpr
    refine ⟨mem_univ _, by omega, ?_⟩
    rw [ha₁]
    simpa only [hroot] using h₁
  · apply mem_filter.mpr
    refine ⟨mem_univ _, by omega, ?_⟩
    rw [ha₀]
    simpa only [hroot] using h₀
