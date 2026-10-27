import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# WiringDiagramPair

Topic: np_completeness   Node: d17c0e50e88f

Provenance: formalization of a published result. Source: arXiv:2610.03808 Sec. 2

An instance of the zero excess problem consisting of a wire count m and two rank-3 signotopes u and v on Fin m representing wiring diagrams of m pseudolines.
-/

/-- An instance of the zero excess problem consisting of m wires and two rank-3 signotopes. -/
structure WiringDiagramPair where
  m : ℕ
  u : OrderedTriple (Fin m) → ℤˣ
  v : OrderedTriple (Fin m) → ℤˣ
  hu : is_rank_three_signotope u
  hv : is_rank_three_signotope v
