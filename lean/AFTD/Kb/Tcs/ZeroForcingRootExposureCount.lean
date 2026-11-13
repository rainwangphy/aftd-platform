import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForcingRootExposedFort

/-!
# zero_forcing_root_exposure_count

Topic: graphs   Node: c41eb26f4a57

Provenance: helper lemma. Counts the rooted boundary states in the four-state recurrence towards OP-1399.

The number of k-element white vertex sets whose complement is zero forcing and whose root-exposed-fort status equals the given Boolean.
-/

noncomputable def zero_forcing_root_exposure_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) (k : ℕ) (exposed : Bool) : ℕ := {W : Finset V | W.card = k ∧ is_zero_forcing_set G ((Finset.univ \ W : Finset V) : Set V) ∧ ((exposed = true) ↔ zero_forcing_root_exposed_fort G r W)}.ncard
