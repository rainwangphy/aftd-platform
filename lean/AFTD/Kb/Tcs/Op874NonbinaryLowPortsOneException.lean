import AFTD.Prelude
import AFTD.Kb.Tcs.Op874NonbinaryFixedLowPortData
import AFTD.Kb.Tcs.Op874NonbinaryBit

/-!
# op874_nonbinary_low_ports_one_exception

Topic: graphs   Node: dd7e8a4d803c

Provenance: helper lemma. Explicit fixed-low local-to-global obstruction, experiments 36317–36319.

The explicit matching and selected low ports are consistent, cover same-bit factor edges without double selection, and have one reversal from the stated per-cycle directions.
-/

theorem op874_nonbinary_low_ports_one_exception :
  (∀ i, In1098Global.mate (In1098Global.mate i) = i ∧ In1098Global.mate i ≠ i ∧ op874_nonbinary_bit (In1098Global.mate i) = op874_nonbinary_bit i ∧ In1098Global.prev (In1098Global.next i) = i ∧ In1098Global.next (In1098Global.prev i) = i) ∧
  (∀ i, In1098Global.selected i = In1098Global.mate i ∨ In1098Global.selected i = In1098Global.prev i ∨ In1098Global.selected i = In1098Global.next i) ∧
  (∀ i, In1098Global.selected i = In1098Global.mate i ↔ In1098Global.selected (In1098Global.mate i) ≠ i) ∧
  (∀ i, op874_nonbinary_bit i = op874_nonbinary_bit (In1098Global.next i) → In1098Global.selected i = In1098Global.next i ∨ In1098Global.selected (In1098Global.next i) = i) ∧
  (∀ i, ¬ (In1098Global.selected i = In1098Global.next i ∧ In1098Global.selected (In1098Global.next i) = i)) ∧
  (∀ i, In1098Global.selected i ≠ In1098Global.mate i → (i = 6 ∧ In1098Global.selected i = In1098Global.prev i) ∨ (i ≠ 6 ∧ (if In1098Global.group i = 3 then In1098Global.selected i = In1098Global.prev i else In1098Global.selected i = In1098Global.next i))) := by decide
