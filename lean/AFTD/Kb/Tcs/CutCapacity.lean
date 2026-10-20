import AFTD.Prelude
import AFTD.Kb.Tcs.CapacitatedNetwork

/-!
# cutCapacity

Topic: information   Node: 484089972691

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

The total capacity of the edges of the network leaving a vertex set S: the sum over u ∈ S and all v of cap({u,v}), with the terms where v ∈ S set to zero.
-/

/-- Total capacity leaving the cut S. -/
def cutCapacity {V : Type} [Fintype V] [DecidableEq V] (net : CapacitatedNetwork V) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v, if v ∈ S then 0 else net.cap s(u, v)
