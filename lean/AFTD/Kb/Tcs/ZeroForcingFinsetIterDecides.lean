import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingFinsetStep
import AFTD.Kb.Tcs.ZeroForcingFinsetIter
import AFTD.Kb.Tcs.ZeroForcingFinsetIterOfStable
import AFTD.Kb.Tcs.FinsetInflationaryIterStableAtCard
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zero_forcing_finset_iter_decides

Topic: graphs   Node: aacf6754ce97

Provenance: helper lemma.

A blue set is zero forcing exactly when the executable parallel forcing process colors every vertex after at most the number of vertices many iterations.
-/

theorem zero_forcing_finset_iter_decides {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : is_zero_forcing_set G (S : Set V) ↔ zero_forcing_finset_iter G S (Fintype.card V) = Finset.univ := by
  apply zero_forcing_finset_iter_of_stable
  change zero_forcing_finset_step G ((zero_forcing_finset_step G)^[Fintype.card V] S) = _
  apply finset_inflationary_iter_stable_at_card
  intro colored
  exact Finset.subset_union_left
