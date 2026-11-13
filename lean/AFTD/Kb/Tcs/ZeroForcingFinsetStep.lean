import AFTD.Prelude

/-!
# zero_forcing_finset_step

Topic: graphs   Node: 203777f3d9e4

Provenance: helper lemma.

One executable parallel zero forcing step from a finite blue set: include each vertex with a blue neighbor whose other neighbors are blue.
-/

def zero_forcing_finset_step {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V := S ∪ Finset.univ.filter (fun w => ∃ u ∈ S, G.Adj u w ∧ ∀ x, G.Adj u x → x ≠ w → x ∈ S)
