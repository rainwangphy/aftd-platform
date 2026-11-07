import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# nat_self_delimiting_code_zero

Topic: computability   Node: f95ce9c75a23

Provenance: helper lemma. Sanity check of nat_self_delimiting_code (OP-851 encoding).

The self-delimiting code of 0 is the single bit false.
-/

theorem nat_self_delimiting_code_zero : nat_self_delimiting_code 0 = [false] := by
  simp [nat_self_delimiting_code]
