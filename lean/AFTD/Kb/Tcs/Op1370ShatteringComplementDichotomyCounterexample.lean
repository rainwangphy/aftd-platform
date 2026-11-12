import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented

/-!
# op_1370_shattering_complement_dichotomy_counterexample

Topic: combinatorics   Node: 1ce54443c616

Provenance: helper lemma. Counterexample to a possible shattering dichotomy encountered while studying arXiv:2611.12199, Conjecture 4.3.

There is an uncomplemented family of subsets of Fin 6 which shatters both {0,1,2} and its complement {3,4,5}, while it shatters neither {0,2,3} nor its complement {1,4,5}.
-/

open Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
def op1370_eight_sets : Finset (Finset (Fin 6)) := {∅, {0,3}, {1,4}, {0,1,3,4}, {0,2,5}, {2,3,5}, {0,1,2,4,5}, {1,2,3,4,5}}

theorem op_1370_shattering_complement_dichotomy_counterexample : ∃ F : Finset (Finset (Fin 6)), is_uncomplemented F ∧ ({0,1,2} : Finset (Fin 6)) ∈ F.shatterer ∧ ({3,4,5} : Finset (Fin 6)) ∈ F.shatterer ∧ ({0,2,3} : Finset (Fin 6)) ∉ F.shatterer ∧ ({1,4,5} : Finset (Fin 6)) ∉ F.shatterer := by
  refine ⟨op1370_eight_sets, ?_, ?_, ?_, ?_, ?_⟩
  · unfold is_uncomplemented; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
