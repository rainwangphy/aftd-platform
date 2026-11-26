import AFTD.Prelude

/-!
# op309_three_pair_conflict_kernel

Topic: graphs   Node: 361f632624b6

Provenance: helper lemma. OP-309 local P3 port pairing obstruction; experiments 41711-41716.

Three port-pair constraints conflict with the listed inequalities.
-/

theorem op309_three_pair_conflict_kernel {α : Type*}
    (x7 x8 x10 x12 x14 x16 x17 : α)
    (hA : x12=x17 ∨ x12=x8)
    (hB : x7=x10 ∨ x7=x16)
    (hC : (x12=x16 ∧ x14=x17) ∨ (x12=x17 ∧ x14=x16))
    (n7_10 : x7≠x10) (n7_14 : x7≠x14) (n7_8 : x7≠x8) : False := by
  set_option maxHeartbeats 4000000 in
    rcases hA with hA | hA <;>
    rcases hB with hB | hB <;>
    rcases hC with ⟨hC1,hC2⟩ | ⟨hC1,hC2⟩ <;> simp_all
