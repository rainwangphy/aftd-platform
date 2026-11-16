import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_twoblock_nonprivate_equality_counterexample

Topic: combinatorics   Node: b96b456cf966

Provenance: original. Related work: Counterexample to a proposed two-family equality-structure route for OP-1370, arXiv:2611.12199, Conjecture 4.3.

There exist two strongly incomparable uncomplemented families of subsets of a six-element set, each varying at every coordinate, whose total size is 32. Equality for two families therefore does not force a coordinate to be uniformly present or absent in one of the families.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
def op1370_twoblock_eq_a : Finset (Finset (Fin 6)) := {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 4}, {1, 4}, {0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {0, 1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {0, 1, 3, 4}, {0, 1, 5}, {0, 4, 5}, {1, 4, 5}, {0, 1, 4, 5}}
def op1370_twoblock_eq_b : Finset (Finset (Fin 6)) := {{2, 3}, {0, 2, 3}, {1, 2, 3}, {2, 3, 4}, {2, 5}, {0, 2, 5}, {1, 2, 5}, {3, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 2, 3, 5}, {1, 2, 3, 5}, {2, 4, 5}, {3, 4, 5}, {2, 3, 4, 5}}
def op1370_twoblock_eq_f : Fin 2 → Finset (Finset (Fin 6)) := ![op1370_twoblock_eq_a, op1370_twoblock_eq_b]
lemma op1370_twoblock_eq_a_uncomp : is_uncomplemented op1370_twoblock_eq_a := by unfold is_uncomplemented; decide +kernel
lemma op1370_twoblock_eq_b_uncomp : is_uncomplemented op1370_twoblock_eq_b := by unfold is_uncomplemented; decide +kernel
lemma op1370_twoblock_eq_f_uncomp : ∀ i, is_uncomplemented (op1370_twoblock_eq_f i) := by
  intro i; fin_cases i <;> simp [op1370_twoblock_eq_f, op1370_twoblock_eq_a_uncomp, op1370_twoblock_eq_b_uncomp]
lemma op1370_twoblock_eq_f_incomp : strongly_incomparable op1370_twoblock_eq_f := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_twoblock_eq_f_vary : ∀ i : Fin 2, ∀ x : Fin 6, (∃ S ∈ op1370_twoblock_eq_f i, x ∈ S) ∧ (∃ T ∈ op1370_twoblock_eq_f i, x ∉ T) := by
  decide +kernel
lemma op1370_twoblock_eq_f_card : ∑ i, (op1370_twoblock_eq_f i).card = 2^5 := by decide +kernel

theorem op_1370_twoblock_nonprivate_equality_counterexample : ∃ 𝒜 : Fin 2 → Finset (Finset (Fin 6)),
      (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧
      (∀ i, ∀ x, (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 i, x ∉ T)) ∧
      (∑ i, (𝒜 i).card = 2^5) := by
  exact ⟨op1370_twoblock_eq_f, op1370_twoblock_eq_f_uncomp, op1370_twoblock_eq_f_incomp, op1370_twoblock_eq_f_vary, op1370_twoblock_eq_f_card⟩
