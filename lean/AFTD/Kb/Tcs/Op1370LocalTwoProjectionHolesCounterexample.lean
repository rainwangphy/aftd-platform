import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_local_two_projection_holes_counterexample

Topic: combinatorics   Node: 42324a2bb412

Provenance: helper lemma. Counterexample to a proposed strengthening of op_1370_no_private_fiber_count, related to arXiv:2611.12199, Conjecture 4.3.

There are three nonempty uncomplemented mutually strongly incomparable families on Fin 5 for which element 0 occurs in at least two families and is absent in at least two families, yet erasing 0 from their union gives 14 distinct subsets of the other four elements. Thus the local incidence assumptions alone do not force more than two missing projected fibers.
-/

open Finset
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
def op1370_twoholes_f0 : Finset (Finset (Fin 5)) := {{1,3,4}}
def op1370_twoholes_f1 : Finset (Finset (Fin 5)) := {{0,2}, {1,2}, {2,3}, {1,2,3}, {2,4}, {1,2,4}, {2,3,4}}
def op1370_twoholes_f2 : Finset (Finset (Fin 5)) := {{0,1}, {0,3}, {0,1,3}, {0,4}, {0,1,4}, {0,3,4}}
def op1370_twoholes_families : Fin 3 → Finset (Finset (Fin 5)) := ![op1370_twoholes_f0, op1370_twoholes_f1, op1370_twoholes_f2]
lemma op1370_twoholes_nonempty : ∀ i, (op1370_twoholes_families i).Nonempty := by decide +kernel
lemma op1370_twoholes_unc : ∀ i, is_uncomplemented (op1370_twoholes_families i) := by
  unfold is_uncomplemented
  decide +kernel
lemma op1370_twoholes_inc : strongly_incomparable op1370_twoholes_families := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_twoholes_pos : ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ op1370_twoholes_families i, (0 : Fin 5) ∈ S) ∧ (∃ T ∈ op1370_twoholes_families j, (0 : Fin 5) ∈ T) := by decide +kernel
lemma op1370_twoholes_neg : ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ op1370_twoholes_families i, (0 : Fin 5) ∉ S) ∧ (∃ T ∈ op1370_twoholes_families j, (0 : Fin 5) ∉ T) := by decide +kernel
lemma op1370_twoholes_card : ((Finset.univ.biUnion op1370_twoholes_families).image (fun S => S.erase (0 : Fin 5))).card = 14 := by decide +kernel

theorem op_1370_local_two_projection_holes_counterexample : ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 5)), (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧ (∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, (0 : Fin 5) ∈ S) ∧ (∃ T ∈ 𝒜 j, (0 : Fin 5) ∈ T)) ∧ (∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, (0 : Fin 5) ∉ S) ∧ (∃ T ∈ 𝒜 j, (0 : Fin 5) ∉ T)) ∧ ((Finset.univ.biUnion 𝒜).image (fun S => S.erase (0 : Fin 5))).card = 14 := by
  exact ⟨op1370_twoholes_families, op1370_twoholes_nonempty, op1370_twoholes_unc, op1370_twoholes_inc, op1370_twoholes_pos, op1370_twoholes_neg, op1370_twoholes_card⟩
