import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat

/-!
# gpa_nbr_ge

Topic: mechanism_design   Node: 818fc078e0dd

A single neighbour's coordinate is bounded by the neighbour sum.
-/

open Finset in
/-- A single neighbour's coordinate is bounded by the neighbour sum. -/
lemma gpa_nbr_ge {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (σ : Fin k → ℝ) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin k) (hij : G.Adj i j) :
    σ j ≤ ∑ l, gpa_adjMat G i l * σ l := by
  have h1 : gpa_adjMat G i j * σ j = σ j := by simp [gpa_adjMat, hij]
  rw [← h1]
  apply Finset.single_le_sum (f := fun l => gpa_adjMat G i l * σ l)
  · intro l _
    unfold gpa_adjMat
    split_ifs <;> nlinarith [hσ l]
  · exact Finset.mem_univ j
