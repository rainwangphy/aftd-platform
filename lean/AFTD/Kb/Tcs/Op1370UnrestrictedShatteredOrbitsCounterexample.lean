import AFTD.Prelude

/-!
# op_1370_unrestricted_shattered_orbits_counterexample

Topic: combinatorics   Node: cbb754944da0

Provenance: helper lemma. Counterexample to a proposed unrestricted shattered-orbit inequality while studying arXiv:2611.12199, Conjecture 4.3.

There is a family of eight subsets of Fin 4, all incomparable to {0,1}, whose shattered sets occupy only seven complementary orbits.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
def op1370_arbitrary_orbit_family : Finset (Finset (Fin 4)) := {{2}, {1,2}, {3}, {0,3}, {1,3}, {2,3}, {0,2,3}, {1,2,3}}

theorem op_1370_unrestricted_shattered_orbits_counterexample : ∃ F : Finset (Finset (Fin 4)), F.card = 8 ∧ (∀ S ∈ F, ¬ ({0,1} : Finset (Fin 4)) ⊆ S ∧ ¬ S ⊆ ({0,1} : Finset (Fin 4))) ∧ (F.shatterer ∪ F.shatterer.image compl).card = 14 := by
  refine ⟨op1370_arbitrary_orbit_family, ?_, ?_, ?_⟩ <;> decide +kernel
