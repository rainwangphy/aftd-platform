import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingFinsetStep

/-!
# zero_forcing_finset_iter

Topic: graphs   Node: 4cd709b36639

Provenance: helper lemma.

The finite blue set obtained by iterating the executable parallel zero forcing step k times.
-/

def zero_forcing_finset_iter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (k : ℕ) : Finset V := (zero_forcing_finset_step G)^[k] S
