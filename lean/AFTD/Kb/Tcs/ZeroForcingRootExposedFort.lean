import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForced

/-!
# zero_forcing_root_exposed_fort

Topic: graphs   Node: be565b3145d8

Provenance: helper lemma. Rooted-fort boundary state used for the four-state recurrence towards OP-1399; experiment 24723 checks it against direct fort enumeration.

A white set W contains a root-exposed fort if it contains a set F not containing r such that r has a neighbor in F and every vertex other than r outside F has either zero or at least two neighbors in F.
-/

def zero_forcing_root_exposed_fort {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) (W : Finset V) : Prop := ∃ F : Finset V, F ⊆ W ∧ r ∉ F ∧ (∃ w ∈ F, G.Adj r w) ∧ ∀ u : V, u ≠ r → u ∉ F → ∀ w : V, w ∈ F → G.Adj u w → ∃ x : V, x ∈ F ∧ G.Adj u x ∧ x ≠ w
