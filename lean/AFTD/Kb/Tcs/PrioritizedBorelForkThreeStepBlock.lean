import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_three_step_block

Topic: automata   Node: c6e439f2e233

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

A three-edge stay or excursion with common output directions false, false, then the supplied bit.
-/

def prioritized_borel_fork_three_step_block (b exit : Bool) : List PrioritizedBorelForkEdge :=
  if exit then
    [⟨0, false, 1, 0⟩, ⟨1, false, 2, 0⟩, ⟨2, b, 0, if b then 1 else 2⟩]
  else
    [⟨0, false, 0, 0⟩, ⟨0, false, 0, 0⟩, ⟨0, b, 0, 0⟩]
