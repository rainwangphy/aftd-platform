import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_two_exception_capacity_counterexample

Topic: combinatorics   Node: d152c299079b

Provenance: helper lemma. Counterexample to a proposed two-exception generalization of op_1370_shattered_capacity, related to arXiv:2611.12199, Conjecture 4.3.

There are four nonempty mutually strongly incomparable families on Fin 5, with the first two uncomplemented and with element 0 absent from the last two; the first two families have four sets each, while the union of the last two shatters nine sets. Thus eight plus nine exceeds the 16 subsets of the other four coordinates, disproving the direct two-exception extension of the private-element shattering-capacity inequality.
-/

open Finset
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
def op1370_cap2_f0 : Finset (Finset (Fin 5)) := {{0,1}, {0,3}, {1,3}, {0,1,3}}
def op1370_cap2_f1 : Finset (Finset (Fin 5)) := {{0,2}, {0,4}, {2,4}, {0,2,4}}
def op1370_cap2_f2 : Finset (Finset (Fin 5)) := {{1,2}, {1,4}, {3,4}}
def op1370_cap2_f3 : Finset (Finset (Fin 5)) := {{2,3}}
def op1370_cap2_families : Fin 4 → Finset (Finset (Fin 5)) := ![op1370_cap2_f0, op1370_cap2_f1, op1370_cap2_f2, op1370_cap2_f3]
lemma op1370_cap2_nonempty : ∀ i, (op1370_cap2_families i).Nonempty := by decide +kernel
lemma op1370_cap2_inc : strongly_incomparable op1370_cap2_families := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_cap2_unc : is_uncomplemented op1370_cap2_f0 ∧ is_uncomplemented op1370_cap2_f1 := by
  unfold is_uncomplemented
  decide +kernel
lemma op1370_cap2_nozero : (∀ S ∈ op1370_cap2_f2, (0 : Fin 5) ∉ S) ∧ (∀ S ∈ op1370_cap2_f3, (0 : Fin 5) ∉ S) := by decide +kernel
lemma op1370_cap2_counts : op1370_cap2_f0.card = 4 ∧ op1370_cap2_f1.card = 4 ∧ (op1370_cap2_f2 ∪ op1370_cap2_f3).shatterer.card = 9 := by decide +kernel

theorem op_1370_two_exception_capacity_counterexample : ∃ 𝒜 : Fin 4 → Finset (Finset (Fin 5)), (∀ i, (𝒜 i).Nonempty) ∧ strongly_incomparable 𝒜 ∧ is_uncomplemented (𝒜 0) ∧ is_uncomplemented (𝒜 1) ∧ (∀ S ∈ 𝒜 2, (0 : Fin 5) ∉ S) ∧ (∀ S ∈ 𝒜 3, (0 : Fin 5) ∉ S) ∧ (𝒜 0).card = 4 ∧ (𝒜 1).card = 4 ∧ (𝒜 2 ∪ 𝒜 3).shatterer.card = 9 := by
  exact ⟨op1370_cap2_families, op1370_cap2_nonempty, op1370_cap2_inc, op1370_cap2_unc.1, op1370_cap2_unc.2, op1370_cap2_nozero.1, op1370_cap2_nozero.2, op1370_cap2_counts.1, op1370_cap2_counts.2.1, op1370_cap2_counts.2.2⟩
