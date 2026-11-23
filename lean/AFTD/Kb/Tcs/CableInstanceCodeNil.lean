import AFTD.Prelude
import AFTD.Kb.Tcs.CableInstanceCode

/-!
# cable_instance_code_nil

Topic: approximation   Node: 2cdc80bd364d

Provenance: helper lemma. Sanity check of cable_instance_code.

The empty instance is encoded by the single bit false.
-/

theorem cable_instance_code_nil : cable_instance_code [] = [false] := by decide
