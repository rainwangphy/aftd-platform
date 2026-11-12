import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_global_two_projection_holes_counterexample

Topic: combinatorics   Node: 78bfdd3cdee7

Provenance: helper lemma. Counterexample to a proposed four-missing-projection-fibers strengthening related to arXiv:2611.12199, Conjecture 4.3.

There are four nonempty uncomplemented mutually strongly incomparable families on Fin 5 with both no-private incidence conditions at every element, but only two subsets of the other four elements are missing after erasing element 0 from their union.
-/

open Finset
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
def op1370_globalholes_f0 : Finset (Finset (Fin 5)) := {{0, 1}}
def op1370_globalholes_f1 : Finset (Finset (Fin 5)) := {{2, 3, 4}}
def op1370_globalholes_f2 : Finset (Finset (Fin 5)) := {{1, 2}, {1, 3}, {1, 2, 3}, {1, 4}, {1, 2, 4}, {1, 3, 4}}
def op1370_globalholes_f3 : Finset (Finset (Fin 5)) := {{0, 2}, {0, 3}, {0, 2, 3}, {0, 4}, {0, 2, 4}, {0, 3, 4}}
def op1370_globalholes_families : Fin 4 → Finset (Finset (Fin 5)) := ![op1370_globalholes_f0, op1370_globalholes_f1, op1370_globalholes_f2, op1370_globalholes_f3]
lemma op1370_globalholes_ne : ∀ i, (op1370_globalholes_families i).Nonempty := by decide +kernel
lemma op1370_globalholes_unc : ∀ i, is_uncomplemented (op1370_globalholes_families i) := by
  unfold is_uncomplemented
  decide +kernel
lemma op1370_globalholes_inc : strongly_incomparable op1370_globalholes_families := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_globalholes_pos : ∀ x : Fin 5, ∃ i j : Fin 4, i ≠ j ∧ (∃ S ∈ op1370_globalholes_families i, x ∈ S) ∧ (∃ T ∈ op1370_globalholes_families j, x ∈ T) := by decide +kernel
lemma op1370_globalholes_neg : ∀ x : Fin 5, ∃ i j : Fin 4, i ≠ j ∧ (∃ S ∈ op1370_globalholes_families i, x ∉ S) ∧ (∃ T ∈ op1370_globalholes_families j, x ∉ T) := by decide +kernel
lemma op1370_globalholes_card : ((Finset.univ.biUnion op1370_globalholes_families).image (fun S => S.erase (0 : Fin 5))).card = 14 := by decide +kernel

theorem op_1370_global_two_projection_holes_counterexample : ∃ 𝒜 : Fin 4 → Finset (Finset (Fin 5)), (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧ (∀ x, ∃ i j : Fin 4, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)) ∧ (∀ x, ∃ i j : Fin 4, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)) ∧ ((Finset.univ.biUnion 𝒜).image (fun S => S.erase (0 : Fin 5))).card = 14 := by
  exact ⟨op1370_globalholes_families, op1370_globalholes_ne, op1370_globalholes_unc, op1370_globalholes_inc, op1370_globalholes_pos, op1370_globalholes_neg, op1370_globalholes_card⟩
