import AFTD.Prelude
import AFTD.Kb.Tcs.G5Adj

/-!
# g5_adj_symm

Topic: graphs   Node: 67a9fc96b79e

Provenance: helper lemma. sanity lemma for g5_adj (arXiv:2610.21388, Def. 2.1, t = 5)

Sanity lemma: the adjacency of G_5 is symmetric.
-/

theorem g5_adj_symm (i j : Fin 5) (h : g5_adj i j) : g5_adj j i := by
  fin_cases i <;> fin_cases j <;> simp_all [g5_adj]
