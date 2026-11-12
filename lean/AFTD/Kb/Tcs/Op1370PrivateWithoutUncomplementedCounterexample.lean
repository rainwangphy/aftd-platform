import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_private_without_uncomplemented_counterexample

Topic: combinatorics   Node: 0f17c60ff870

Provenance: helper lemma. Counterexample to dropping an assumption of op_1370_private_element_bound, related to arXiv:2611.12199, Conjecture 4.3.

There are three nonempty mutually strongly incomparable families of subsets of Fin 4 for which element 0 appears only in the first family, the total size is eight, and the first family contains a complementary pair. Thus the private-element bound fails if uncomplementedness of the exceptional family is removed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
def op1370_private_unc_f0 : Finset (Finset (Fin 4)) := {{0}, {0,1}, {0,2}, {0,3}, {2,3}, {0,2,3}}
def op1370_private_unc_f1 : Finset (Finset (Fin 4)) := {{1,2}}
def op1370_private_unc_f2 : Finset (Finset (Fin 4)) := {{1,3}}
def op1370_private_unc_families : Fin 3 → Finset (Finset (Fin 4)) := ![op1370_private_unc_f0, op1370_private_unc_f1, op1370_private_unc_f2]

theorem op_1370_private_without_uncomplemented_counterexample : ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 4)), (∀ i, (𝒜 i).Nonempty) ∧ strongly_incomparable 𝒜 ∧ (∀ j : Fin 3, j ≠ 0 → ∀ S ∈ 𝒜 j, (0 : Fin 4) ∉ S) ∧ (∑ i, (𝒜 i).card) = 8 ∧ ¬ is_uncomplemented (𝒜 0) := by
  refine ⟨op1370_private_unc_families, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · unfold strongly_incomparable; decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold is_uncomplemented; decide +kernel
