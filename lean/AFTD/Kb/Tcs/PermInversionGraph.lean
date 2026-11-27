import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# perm_inversion_graph

Topic: combinatorics   Node: 5f11e73dc8fc

Provenance: formalization of a published result. Source: arXiv:2611.33575 Section 1

The inversion graph of a permutation $\sigma$ on $\{0, \dots, n-1\}$ has vertex set $\{0, \dots, n-1\}$ and an edge between $i$ and $j$ if and only if $i$ and $j$ form an inversion of $\sigma$.
-/

/-- The inversion graph of a permutation on Fin n, where two indices are adjacent if they form an inversion. -/
def perm_inversion_graph {n : ℕ} (σ : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) := {
  Adj := fun i j => (i < j ∧ σ j < σ i) ∨ (j < i ∧ σ i < σ j)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i => by rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact lt_irrefl i h⟩
}
