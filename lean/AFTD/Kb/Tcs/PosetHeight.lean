import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# poset_height

Topic: combinatorics   Node: 840b068cddd7

Provenance: helper lemma. step towards op314_poset_tower_two_cancellation

The height of a finite partial order α: one less than the maximum cardinality of a chain in α, i.e. the largest n such that α admits a strictly increasing map Fin (n+1) → α. Equals 0 for an empty order and for an antichain.
-/

/-- Height of a finite partial order: the supremum of the n for which there is a strictly increasing family Fin (n+1) → α, i.e. one less than the size of a longest chain. -/
noncomputable def poset_height (α : Type*) [PartialOrder α] [Fintype α] : ℕ := sSup {n : ℕ | ∃ f : Fin (n+1) → α, StrictMono f}
