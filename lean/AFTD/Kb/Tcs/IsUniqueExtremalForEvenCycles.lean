import AFTD.Prelude
import AFTD.Kb.Tcs.EvenCycleExtremalGraph

/-!
# is_unique_extremal_for_even_cycles

Topic: combinatorics   Node: 71c3e6480ddb

Provenance: formalization of a published result. Source: arXiv:2611.24238 Sec. 1, Theorem 1.1

For integers $n, k, \ell$, $H_{n,k}$ is the unique $n$-vertex $C_{2k}$-free graph maximizing the number of unlabeled copies of $C_{2\ell}$.
-/

/-- Predicate asserting that H_{n,k} is the unique C_{2k}-free graph on n vertices maximizing the number of C_{2l} copies. -/
def is_unique_extremal_for_even_cycles (n k l : ℕ) : Prop :=
  let H := even_cycle_extremal_graph n k
  (SimpleGraph.cycleGraph (2 * k)).Free H ∧
  ∀ (G : SimpleGraph (Fin n)), (SimpleGraph.cycleGraph (2 * k)).Free G →
    G.copyCount (SimpleGraph.cycleGraph (2 * l)) ≤ H.copyCount (SimpleGraph.cycleGraph (2 * l)) ∧
    (G.copyCount (SimpleGraph.cycleGraph (2 * l)) = H.copyCount (SimpleGraph.cycleGraph (2 * l)) → Nonempty (G ≃g H))
