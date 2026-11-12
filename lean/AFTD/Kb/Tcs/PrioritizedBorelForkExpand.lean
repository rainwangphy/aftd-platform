import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock

/-!
# prioritized_borel_fork_expand

Topic: automata   Node: 8faec0bfca30

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Expand equally indexed visible bits and hidden stay-or-excursion choices into three-edge blocks.
-/

def prioritized_borel_fork_expand : List Bool → List Bool → List PrioritizedBorelForkEdge
  | b :: u, c :: h => prioritized_borel_fork_three_step_block b c ++ prioritized_borel_fork_expand u h
  | _, _ => []
