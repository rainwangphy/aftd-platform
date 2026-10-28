import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_class_weight_eq_of_sum_eq

Topic: combinatorics   Node: 102557ff470c

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

If the total sum of dyadic class weights over all residues equals the total sum of active counts, then pointwise equality holds for every residue.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- If the total sum of dyadic class weights over all residues equals the total sum of active counts, then pointwise equality holds for every residue. -/
theorem cycle_power_dyadic_class_weight_eq_of_sum_eq
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m) (b : ZMod n → ℕ → Bool)
    (hsum : (∑ p : ZMod n, cycle_power_dyadic_class_weight m (b p)) =
      ∑ p : ZMod n, (Finset.range (2 ^ m)).sum (fun a => (b p a).toNat)) :
    ∀ p : ZMod n, cycle_power_dyadic_class_weight m (b p) =
      (Finset.range (2 ^ m)).sum (fun a => (b p a).toNat) := by
  intro p
  have hle := cycle_power_dyadic_class_weight_le m hm (b p)
  by_contra hne
  have hlt : cycle_power_dyadic_class_weight m (b p) < (Finset.range (2^m)).sum (fun a => (b p a).toNat) := by omega
  have hslt := sum_lt_sum (fun q _ => cycle_power_dyadic_class_weight_le m hm (b q))
    ⟨p, mem_univ _, hlt⟩
  omega
