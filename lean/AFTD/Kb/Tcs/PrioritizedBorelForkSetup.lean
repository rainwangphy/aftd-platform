import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_setup

Topic: automata   Node: b42791b8a577

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

The first two forced edges of a fork excursion.
-/

def prioritized_borel_fork_setup : List PrioritizedBorelForkEdge :=
  [⟨0, false, 1, 0⟩, ⟨1, false, 2, 0⟩]
