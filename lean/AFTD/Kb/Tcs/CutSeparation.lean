import AFTD.Prelude
import AFTD.Kb.Tcs.UnicastSessions

/-!
# cutSeparation

Topic: information   Node: 2b1ccc77c157

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

The number of sessions (out of the unicast session set sess) with exactly one endpoint in the vertex set S, i.e. the number of sessions separated by the cut S.
-/

/-- Number of sessions crossing the cut S. -/
def cutSeparation {V : Type} [DecidableEq V] {K : Type} [Fintype K] (sess : UnicastSessions V K) (S : Finset V) : ℕ := (Finset.univ.filter (fun k => (sess.src k ∈ S) ≠ (sess.tgt k ∈ S))).card
