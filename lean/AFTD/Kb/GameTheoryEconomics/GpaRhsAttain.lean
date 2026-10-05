import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaCube
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaNbrNonneg

/-!
# gpa_rhs_attain

Topic: mechanism_design   Node: 1882adfadd33

The value α(G) is attained on the cube, at the indicator vector of a maximum independent set.
-/

open Finset in
/-- The value `α(G)` is attained on the cube, at the indicator vector of a maximum independent set. -/
lemma gpa_rhs_attain {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (I : Finset (Fin k)) (hI : gpa_indep G I) :
    (fun i => if i ∈ I then (1 : ℝ) else 0) ∈ gpa_cube k ∧
      gpa_uStar (gpa_adjMat G) (fun i => if i ∈ I then (1 : ℝ) else 0) = I.card := by
  classical
  refine ⟨fun i => by dsimp only; constructor <;> split_ifs <;> norm_num, ?_⟩
  unfold gpa_uStar
  have hterm : ∀ i, max ((if i ∈ I then (1 : ℝ) else 0) -
      ∑ j, gpa_adjMat G i j * (if j ∈ I then (1 : ℝ) else 0)) 0 =
      if i ∈ I then 1 else 0 := by
    intro i
    by_cases hi : i ∈ I
    · have hz : ∑ j, gpa_adjMat G i j * (if j ∈ I then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j ∈ I
        · have : ¬ G.Adj i j := hI i hi j hj
          simp [gpa_adjMat, this]
        · simp [hj]
      rw [hz]; simp [hi]
    · have hnn := gpa_nbr_nonneg G (fun j => if j ∈ I then (1 : ℝ) else 0)
        (fun j => by split_ifs <;> norm_num) i
      simp only [hi, if_false]
      exact max_eq_right (by linarith)
  simp_rw [hterm]
  simp
