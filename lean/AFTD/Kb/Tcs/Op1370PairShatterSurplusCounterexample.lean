import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_pair_shatter_surplus_counterexample

Topic: combinatorics   Node: 993a7de76da3

Provenance: original. Related work: Explicit counterexample to a proposed two-extra-shattered-orbits shortcut toward arXiv:2611.12199, Conjecture 4.3.

There are three families indexed by Fin 3 of subsets of Fin 6, each with nine sets, which are nonempty, uncomplemented, and mutually strongly incomparable; every element appears in at least two families and is absent from at least two families. For each of the pairs (0,1), (0,2), and (1,2), the union of that pair shatters sets whose union with their complements has cardinality 38.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def op1370_family_0 : Finset (Finset (Fin 6)) := {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}, {0, 1, 4}, {0, 1, 3, 4}, {0, 1, 5}, {0, 1, 2, 5}, {0, 1, 4, 5}}
def op1370_family_1 : Finset (Finset (Fin 6)) := {{3, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 2, 3, 5}, {1, 2, 3, 5}, {3, 4, 5}, {0, 3, 4, 5}, {1, 3, 4, 5}}
def op1370_family_2 : Finset (Finset (Fin 6)) := {{2, 4}, {0, 2, 4}, {1, 2, 4}, {2, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {2, 4, 5}, {0, 2, 4, 5}, {1, 2, 4, 5}}

def op1370_families : Fin 3 → Finset (Finset (Fin 6)) := ![op1370_family_0, op1370_family_1, op1370_family_2]
def op1370_orbit_closure (F : Finset (Finset (Fin 6))) : Finset (Finset (Fin 6)) := F.shatterer ∪ F.shatterer.image compl

lemma op1370_family_nonempty : ∀ i, (op1370_families i).Nonempty := by decide +kernel
lemma op1370_family_uncomp : ∀ i, is_uncomplemented (op1370_families i) := by
  unfold is_uncomplemented
  decide +kernel
lemma op1370_family_incomp : strongly_incomparable op1370_families := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_family_coverage : ∀ x : Fin 6, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ op1370_families i, x ∈ S) ∧ (∃ T ∈ op1370_families j, x ∈ T) := by decide +kernel
lemma op1370_family_noncoverage : ∀ x : Fin 6, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ op1370_families i, x ∉ S) ∧ (∃ T ∈ op1370_families j, x ∉ T) := by decide +kernel
lemma op1370_orbit_01 : (op1370_orbit_closure (op1370_family_0 ∪ op1370_family_1)).card = 38 := by decide +kernel
lemma op1370_orbit_02 : (op1370_orbit_closure (op1370_family_0 ∪ op1370_family_2)).card = 38 := by decide +kernel
lemma op1370_orbit_12 : (op1370_orbit_closure (op1370_family_1 ∪ op1370_family_2)).card = 38 := by decide +kernel

theorem op_1370_pair_shatter_surplus_counterexample :
    ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 6)),
      (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧
      strongly_incomparable 𝒜 ∧
      (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)) ∧
      (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)) ∧
      (∀ i, (𝒜 i).card = 9) ∧
      (((𝒜 0 ∪ 𝒜 1).shatterer ∪ ((𝒜 0 ∪ 𝒜 1).shatterer.image compl)).card = 38) ∧
      (((𝒜 0 ∪ 𝒜 2).shatterer ∪ ((𝒜 0 ∪ 𝒜 2).shatterer.image compl)).card = 38) ∧
      (((𝒜 1 ∪ 𝒜 2).shatterer ∪ ((𝒜 1 ∪ 𝒜 2).shatterer.image compl)).card = 38) := by
  refine ⟨op1370_families, op1370_family_nonempty, op1370_family_uncomp, op1370_family_incomp,
    op1370_family_coverage, op1370_family_noncoverage, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide +kernel
  · exact op1370_orbit_01
  · exact op1370_orbit_02
  · exact op1370_orbit_12
