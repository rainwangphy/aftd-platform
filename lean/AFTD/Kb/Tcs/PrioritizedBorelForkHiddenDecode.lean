import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_hidden_decode

Topic: automata   Node: edbdac5ec3b0

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Recover the hidden stay-or-excursion choices from the first edge of each three-edge block.
-/

def prioritized_borel_fork_hidden_decode : List PrioritizedBorelForkEdge → List Bool
  | a :: _ :: _ :: rest => decide (a.dst = 1) :: prioritized_borel_fork_hidden_decode rest
  | _ => []
