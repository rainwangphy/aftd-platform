import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zero_forcing_white_weighted_count

Topic: graphs   Node: 9eae326b1402

Provenance: helper lemma. Weighted counting notation for testing potential strengthenings of the tree zero forcing polynomial question, OP-1399.

The total product weight of k-element white sets whose complement is a zero forcing set.
-/

noncomputable def zero_forcing_white_weighted_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : V → ℕ) (k : ℕ) : ℕ := by
  classical
  exact ∑ S ∈ Finset.univ.filter (fun S : Finset V => S.card = k ∧ is_zero_forcing_set G ((Finset.univ \ S : Finset V) : Set V)), ∏ v ∈ S, w v
