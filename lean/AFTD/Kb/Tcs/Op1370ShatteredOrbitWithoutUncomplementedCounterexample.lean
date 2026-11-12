import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_shattered_orbit_without_uncomplemented_counterexample

Topic: combinatorics   Node: b200069d726c

Provenance: helper lemma. Counterexample to a proposed strengthening of the shattered-orbit route toward arXiv:2611.12199, Conjecture 4.3.

There exist three nonempty strongly incomparable families on four elements such that the first has six members, the second has one, and the orbit closure of the sets shattered by their union has cardinality fourteen; the first family contains a complementary pair. Consequently, the number of shattered complementary orbits can equal the sum of the first two family sizes if their uncomplementedness is omitted.
-/

open Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
def op1370_nouncomp_f0 : Finset (Finset (Fin 4)) := {{1,2}, {3}, {0,3}, {1,3}, {2,3}, {1,2,3}}
def op1370_nouncomp_f1 : Finset (Finset (Fin 4)) := {{0,2}}
def op1370_nouncomp_f2 : Finset (Finset (Fin 4)) := {{0,1}}
def op1370_nouncomp_families : Fin 3 → Finset (Finset (Fin 4)) := ![op1370_nouncomp_f0, op1370_nouncomp_f1, op1370_nouncomp_f2]

theorem op_1370_shattered_orbit_without_uncomplemented_counterexample : ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 4)), (∀ i, (𝒜 i).Nonempty) ∧ strongly_incomparable 𝒜 ∧ (𝒜 0).card = 6 ∧ (𝒜 1).card = 1 ∧ (((𝒜 0 ∪ 𝒜 1).shatterer ∪ ((𝒜 0 ∪ 𝒜 1).shatterer.image compl)).card = 14) ∧ ¬ is_uncomplemented (𝒜 0) := by
  refine ⟨op1370_nouncomp_families, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · unfold strongly_incomparable; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold is_uncomplemented; decide +kernel
