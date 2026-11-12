import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_no_private_stability_sharp_six

Topic: combinatorics   Node: 935c2b97f00c

Provenance: helper lemma. An exact construction for the proposed no-private stability strengthening of arXiv:2611.12199, Conjecture 4.3.

There are three nonempty uncomplemented mutually strongly incomparable families on six elements such that every element appears in sets in two different families, every element is absent from sets in two different families, and the sum of their sizes is 30.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
def op1370_sharp6_f0 : Finset (Finset (Fin 6)) := {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 5}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 1, 2, 5}, {0, 3, 5}, {0, 4, 5}, {1, 4, 5}, {0, 1, 4, 5}}
def op1370_sharp6_f1 : Finset (Finset (Fin 6)) := {{1, 3, 5}}
def op1370_sharp6_f2 : Finset (Finset (Fin 6)) := {{2, 3}, {0, 2, 3}, {1, 2, 3}, {2, 4}, {0, 2, 4}, {1, 2, 4}, {3, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}, {2, 3, 4, 5}}
def op1370_sharp6_families : Fin 3 → Finset (Finset (Fin 6)) := ![op1370_sharp6_f0, op1370_sharp6_f1, op1370_sharp6_f2]
lemma op1370_sharp6_nonempty : ∀ i, (op1370_sharp6_families i).Nonempty := by decide +kernel
lemma op1370_sharp6_unc : ∀ i, is_uncomplemented (op1370_sharp6_families i) := by
  unfold is_uncomplemented
  decide +kernel
lemma op1370_sharp6_inc : strongly_incomparable op1370_sharp6_families := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_sharp6_pos : ∀ x : Fin 6, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ op1370_sharp6_families i, x ∈ S) ∧ (∃ T ∈ op1370_sharp6_families j, x ∈ T) := by decide +kernel
lemma op1370_sharp6_neg : ∀ x : Fin 6, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ op1370_sharp6_families i, x ∉ S) ∧ (∃ T ∈ op1370_sharp6_families j, x ∉ T) := by decide +kernel
lemma op1370_sharp6_card : (∑ i, (op1370_sharp6_families i).card) = 30 := by decide +kernel

theorem op_1370_no_private_stability_sharp_six : ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 6)), (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧ (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)) ∧ (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)) ∧ (∑ i, (𝒜 i).card) = 30 := by
  exact ⟨op1370_sharp6_families, op1370_sharp6_nonempty, op1370_sharp6_unc, op1370_sharp6_inc, op1370_sharp6_pos, op1370_sharp6_neg, op1370_sharp6_card⟩
