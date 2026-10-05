import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat

/-!
# gpa_adjMat_zero_one

Topic: mechanism_design   Node: 1e0da88d363b

The adjacency matrix is a 0/1 matrix, as required in Section 5.3 of arXiv:2209.01146.
-/

/-- The adjacency matrix is a 0/1 matrix, as required in Section 5.3 of arXiv:2209.01146. -/
lemma gpa_adjMat_zero_one {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj] (i j : Fin k) :
    gpa_adjMat G i j = 0 ∨ gpa_adjMat G i j = 1 := by
  unfold gpa_adjMat
  split_ifs <;> simp
