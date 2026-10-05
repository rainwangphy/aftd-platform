import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat

/-!
# gpa_nbr_nonneg

Topic: mechanism_design   Node: 2a7cb2086ce1

Neighbour sums are nonnegative for nonnegative vectors.
-/

open Finset in
/-- Neighbour sums are nonnegative for nonnegative vectors. -/
lemma gpa_nbr_nonneg {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (σ : Fin k → ℝ) (hσ : ∀ i, 0 ≤ σ i) (i : Fin k) :
    0 ≤ ∑ j, gpa_adjMat G i j * σ j := by
  apply Finset.sum_nonneg
  intro j _
  unfold gpa_adjMat
  split_ifs <;> nlinarith [hσ j]
