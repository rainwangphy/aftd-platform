import AFTD.Prelude
import AFTD.Kb.Tcs.BruhatOrderThreeGraph
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_517_zero_excess_of_eq

Topic: np_completeness   Node: d9b0649cb360

Provenance: helper lemma. arXiv:2610.03808 Sec. 2.2

Every rank-3 signotope on Fin m has braid-move excess 0 with respect to itself: the distance in B(m, 2) from u to u is 0, which equals the number of triples on which u differs from u.
-/

/-- Every rank-3 signotope has zero excess to itself. -/
theorem op_517_zero_excess_of_eq (m : ℕ) (u : OrderedTriple (Fin m) → ℤˣ)
    (hu : is_rank_three_signotope u) :
    (bruhat_order_three_graph (Fin m)).dist ⟨u, hu⟩ ⟨u, hu⟩ = {t : OrderedTriple (Fin m) | u t ≠ u t}.ncard := by
  simp
