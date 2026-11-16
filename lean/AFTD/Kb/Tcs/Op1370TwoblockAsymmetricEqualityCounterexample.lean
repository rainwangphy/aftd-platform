import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_twoblock_asymmetric_equality_counterexample

Topic: combinatorics   Node: 2c0fb8ee6f40

Provenance: original. Related work: Counterexample to a proposed two-family equality-structure route for OP-1370, arXiv:2611.12199, Conjecture 4.3.

There exist two strongly incomparable uncomplemented families of subsets of a seven-element set, each varying at every coordinate, with cardinalities 40 and 24. Their total size is 64, and the two families cannot be complements of one another because their sizes differ.
-/

open Finset
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
def op1370_twoblock_asym_a : Finset (Finset (Fin 7)) := {{0, 2}, {1, 2}, {0, 1, 2}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}, {0, 2, 4}, {1, 2, 4}, {0, 1, 2, 4}, {0, 5}, {1, 5}, {0, 1, 5}, {2, 5}, {0, 2, 5}, {1, 2, 5}, {0, 1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {0, 1, 3, 5}, {2, 3, 5}, {0, 2, 3, 5}, {1, 2, 3, 5}, {0, 1, 2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {0, 1, 4, 5}, {2, 4, 5}, {0, 2, 4, 5}, {1, 2, 4, 5}, {0, 1, 2, 4, 5}, {0, 2, 6}, {1, 2, 6}, {0, 1, 2, 6}, {0, 5, 6}, {1, 5, 6}, {0, 1, 5, 6}, {2, 5, 6}, {0, 2, 5, 6}, {1, 2, 5, 6}, {0, 1, 2, 5, 6}}
def op1370_twoblock_asym_b : Finset (Finset (Fin 7)) := {{3, 4}, {0, 3, 4}, {1, 3, 4}, {0, 1, 3, 4}, {2, 3, 4}, {3, 4, 5}, {3, 6}, {0, 3, 6}, {1, 3, 6}, {0, 1, 3, 6}, {2, 3, 6}, {4, 6}, {0, 4, 6}, {1, 4, 6}, {0, 1, 4, 6}, {2, 4, 6}, {3, 4, 6}, {0, 3, 4, 6}, {1, 3, 4, 6}, {0, 1, 3, 4, 6}, {2, 3, 4, 6}, {3, 5, 6}, {4, 5, 6}, {3, 4, 5, 6}}
def op1370_twoblock_asym_f : Fin 2 → Finset (Finset (Fin 7)) := ![op1370_twoblock_asym_a, op1370_twoblock_asym_b]
lemma op1370_twoblock_asym_a_uncomp : is_uncomplemented op1370_twoblock_asym_a := by unfold is_uncomplemented; decide +kernel
lemma op1370_twoblock_asym_b_uncomp : is_uncomplemented op1370_twoblock_asym_b := by unfold is_uncomplemented; decide +kernel
lemma op1370_twoblock_asym_f_uncomp : ∀ i, is_uncomplemented (op1370_twoblock_asym_f i) := by
  intro i; fin_cases i <;> simp [op1370_twoblock_asym_f, op1370_twoblock_asym_a_uncomp, op1370_twoblock_asym_b_uncomp]
lemma op1370_twoblock_asym_f_incomp : strongly_incomparable op1370_twoblock_asym_f := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_twoblock_asym_f_vary : ∀ i : Fin 2, ∀ x : Fin 7, (∃ S ∈ op1370_twoblock_asym_f i, x ∈ S) ∧ (∃ T ∈ op1370_twoblock_asym_f i, x ∉ T) := by
  decide +kernel
lemma op1370_twoblock_asym_f_card : (∑ i, (op1370_twoblock_asym_f i).card) = 2^6 ∧ (op1370_twoblock_asym_f 0).card = 40 ∧ (op1370_twoblock_asym_f 1).card = 24 := by decide +kernel

theorem op_1370_twoblock_asymmetric_equality_counterexample : ∃ 𝒜 : Fin 2 → Finset (Finset (Fin 7)),
      (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧
      (∀ i, ∀ x, (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 i, x ∉ T)) ∧
      (∑ i, (𝒜 i).card = 2^6) ∧ (𝒜 0).card = 40 ∧ (𝒜 1).card = 24 := by
  exact ⟨op1370_twoblock_asym_f, op1370_twoblock_asym_f_uncomp, op1370_twoblock_asym_f_incomp, op1370_twoblock_asym_f_vary, op1370_twoblock_asym_f_card⟩
