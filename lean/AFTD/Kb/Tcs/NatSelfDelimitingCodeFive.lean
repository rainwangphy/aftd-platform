import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# nat_self_delimiting_code_five

Topic: computability   Node: 1d616e49454d

Provenance: helper lemma. Sanity check of nat_self_delimiting_code (OP-851 encoding).

The self-delimiting code of 5 (binary 101, least significant bit first 1,0,1) is true,true, true,false, true,true, false.
-/

theorem nat_self_delimiting_code_five :
    nat_self_delimiting_code 5 = [true, true, true, false, true, true, false] := by
  decide
