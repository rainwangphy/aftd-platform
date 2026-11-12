import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_small_shatterer_threshold_counterexample

Topic: combinatorics   Node: b7b682d4e918

Provenance: helper lemma. Sharpness counterexample for the trace-counting lemma related to arXiv:2611.12199, Conjecture 4.3.

There exist three nonempty uncomplemented mutually strongly incomparable families on Fin 4 such that the first two contain four sets in total, but their union shatters a complementary pair. Thus the strict size condition in the small-shatterer lemma cannot be replaced by a non-strict one, even with a third incomparable family.
-/

open Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
def op1370_threshold_f0 : Finset (Finset (Fin 4)) := {{0,3}, {1,3}}
def op1370_threshold_f1 : Finset (Finset (Fin 4)) := {{0,2}, {1,2}}
def op1370_threshold_f2 : Finset (Finset (Fin 4)) := {{0,1}}
def op1370_threshold_families : Fin 3 → Finset (Finset (Fin 4)) := ![op1370_threshold_f0, op1370_threshold_f1, op1370_threshold_f2]
lemma op1370_threshold_nonempty : ∀ i, (op1370_threshold_families i).Nonempty := by decide +kernel
lemma op1370_threshold_unc : ∀ i, is_uncomplemented (op1370_threshold_families i) := by
  unfold is_uncomplemented
  decide +kernel
lemma op1370_threshold_inc : strongly_incomparable op1370_threshold_families := by
  unfold strongly_incomparable
  decide +kernel
lemma op1370_threshold_count : op1370_threshold_f0.card + op1370_threshold_f1.card = 4 := by decide +kernel
lemma op1370_threshold_shat : ¬ is_uncomplemented (op1370_threshold_f0 ∪ op1370_threshold_f1).shatterer := by
  unfold is_uncomplemented
  decide +kernel

theorem op_1370_small_shatterer_threshold_counterexample : ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 4)), (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧ (𝒜 0).card + (𝒜 1).card = 4 ∧ ¬ is_uncomplemented (𝒜 0 ∪ 𝒜 1).shatterer := by
  exact ⟨op1370_threshold_families, op1370_threshold_nonempty, op1370_threshold_unc, op1370_threshold_inc, op1370_threshold_count, op1370_threshold_shat⟩
