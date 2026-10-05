import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaNbrNonneg
import AFTD.Kb.GameTheoryEconomics.GpaNbrGe

/-!
# gpa_uStar_le_indep

Topic: mechanism_design   Node: 8fe62131ff9b

Key structural lemma: for a nonnegative vector, the coordinates with a positive term of u* form an independent set P, and u*(σ) ≤ Σ_{i ∈ P} σ_i.
-/

open Finset in
/-- Key structural lemma: for a nonnegative vector, the coordinates with a positive term of `u*` form an independent set `P`, and `u*(σ) ≤ Σ_{i ∈ P} σ_i`. -/
lemma gpa_uStar_le_indep {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (σ : Fin k → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ∃ P : Finset (Fin k), gpa_indep G P ∧
      gpa_uStar (gpa_adjMat G) σ ≤ ∑ i ∈ P, σ i := by
  classical
  let P : Finset (Fin k) := univ.filter (fun i => 0 < σ i - ∑ j, gpa_adjMat G i j * σ j)
  refine ⟨P, ?_, ?_⟩
  · intro i hi j hj hadj
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have a1 := gpa_nbr_ge G σ hσ i j hadj
    have a2 := gpa_nbr_ge G σ hσ j i hadj.symm
    linarith
  · unfold gpa_uStar
    rw [← Finset.sum_filter_add_sum_filter_not univ
      (fun i => 0 < σ i - ∑ j, gpa_adjMat G i j * σ j)]
    have h2 : ∑ i ∈ univ.filter (fun i => ¬ (0 < σ i - ∑ j, gpa_adjMat G i j * σ j)),
        max (σ i - ∑ j, gpa_adjMat G i j * σ j) 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact max_eq_right hi
    rw [h2, add_zero]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [max_eq_left hi.le]
    have := gpa_nbr_nonneg G σ hσ i
    linarith
