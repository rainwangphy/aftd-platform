import AFTD.Prelude

/-!
# gpa_adjMat

Topic: mechanism_design   Node: 3f0cc6c78326

The 0/1 matrix e of arXiv:2209.01146, Section 5.3 (taken from the maximum-independent-set instances of the cited convex-maximisation lemma): e i j = 1 iff i and j are adjacent.
-/

/-- The 0/1 matrix `e` of arXiv:2209.01146, Section 5.3 (taken from the maximum-independent-set instances of the cited convex-maximisation lemma): `e i j = 1` iff `i` and `j` are adjacent. -/
noncomputable def gpa_adjMat {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (i j : Fin k) : ℝ :=
  if G.Adj i j then 1 else 0
