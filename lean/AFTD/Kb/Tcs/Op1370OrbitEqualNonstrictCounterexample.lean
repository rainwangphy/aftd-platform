import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented

/-!
# op_1370_orbit_equal_nonstrict_counterexample

Topic: combinatorics   Node: 34a149b6f2f8

Provenance: helper lemma. Counterexample to an orbit-equality simplification in the study of arXiv:2611.12199, Conjecture 4.3.

There is an uncomplemented family of 15 subsets of Fin 5, all incomparable to {0,1}, which shatters 17 sets in exactly 15 complementary orbits. Hence equality between family size and shattered-orbit count does not imply ordinary shattering equality, even with an incomparable witness and with empty and full sets absent.
-/

open Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
def op1370_orbit_equal_family : Finset (Finset (Fin 5)) := {{2}, {0,2}, {1,2}, {3}, {1,3}, {2,3}, {1,2,3}, {4}, {1,4}, {2,4}, {1,2,4}, {3,4}, {2,3,4}, {0,2,3,4}, {1,2,3,4}}

theorem op_1370_orbit_equal_nonstrict_counterexample : ∃ F : Finset (Finset (Fin 5)), is_uncomplemented F ∧ F.card = 15 ∧ (∀ S ∈ F, ¬ ({0,1} : Finset (Fin 5)) ⊆ S ∧ ¬ S ⊆ ({0,1} : Finset (Fin 5))) ∧ (F.shatterer ∪ F.shatterer.image compl).card = 30 ∧ F.shatterer.card = 17 := by
  refine ⟨op1370_orbit_equal_family, ?_, ?_, ?_, ?_, ?_⟩
  · unfold is_uncomplemented; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
