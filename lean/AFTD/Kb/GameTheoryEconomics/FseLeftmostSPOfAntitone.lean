import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseCost
import AFTD.Kb.GameTheoryEconomics.FseInDomain
import AFTD.Kb.GameTheoryEconomics.FseSP
import AFTD.Kb.GameTheoryEconomics.FseLeftmost
import AFTD.Kb.GameTheoryEconomics.FseLeftmostLe
import AFTD.Kb.GameTheoryEconomics.FseLeftmostAttained
import AFTD.Kb.GameTheoryEconomics.FseLeftmostMapsTo

/-!
# fse_leftmost_SP_of_antitone

Topic: mechanism_design   Node: 1f8937d7580d

Key lemma: for every scaling function that is non-negative and non-increasing on [0,1], the leftmost mechanism is strategyproof.
-/

/-- Key lemma: for every scaling function that is non-negative and non-increasing on `[0,1]`, the leftmost mechanism is strategyproof. -/
theorem fse_leftmost_SP_of_antitone {n : ℕ} [NeZero n] (q : ℝ → ℝ)
    (hq : AntitoneOn q (Set.Icc 0 1)) (hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q y) :
    fse_SP q (fse_leftmost (n := n)) := by
  intro x hx i x' hx'
  have hdom' : fse_InDomain (Function.update x i x') := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [hx']
    · simp [Function.update_of_ne hk, hx k]
  set m := fse_leftmost x with hm
  set m' := fse_leftmost (Function.update x i x') with hm'
  have hmI : m ∈ Set.Icc (0 : ℝ) 1 := fse_leftmost_mapsTo x hx
  have hm'I : m' ∈ Set.Icc (0 : ℝ) 1 := fse_leftmost_mapsTo _ hdom'
  have hle : m ≤ x i := fse_leftmost_le x i
  by_cases hmi : m = x i
  · -- the facility is already at the agent's location: cost zero
    have h0 : fse_cost q m (x i) = 0 := by simp [fse_cost, hmi]
    rw [h0]
    exact mul_nonneg (hpos _ hm'I) (abs_nonneg _)
  · -- the leftmost agent is someone else, so a misreport can only move the facility left
    obtain ⟨j, hj⟩ := fse_leftmost_attained x
    have hji : j ≠ i := by
      intro h; subst h; exact hmi hj
    have hm'm : m' ≤ m := by
      have := fse_leftmost_le (Function.update x i x') j
      rw [Function.update_of_ne hji] at this
      show fse_leftmost (Function.update x i x') ≤ fse_leftmost x
      rw [hj]; exact this
    have hlt : m < x i := lt_of_le_of_ne hle hmi
    have hq' : q m ≤ q m' := hq hm'I hmI hm'm
    have h1 : |x i - m| = x i - m := abs_of_pos (by linarith)
    have h2 : |x i - m'| = x i - m' := abs_of_pos (by linarith)
    simp only [fse_cost]
    rw [h1, h2]
    exact mul_le_mul hq' (by linarith) (by linarith) (hpos _ hm'I)
