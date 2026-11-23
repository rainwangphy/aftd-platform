import AFTD.Prelude
import AFTD.Kb.Tcs.RatSelfDelimitingCode

/-!
# rat_self_delimiting_code_zero

Topic: approximation   Node: 55c29d06686a

Provenance: helper lemma. Sanity check of rat_self_delimiting_code.

The code of the rational 0 is false, false, true, true, false.
-/

theorem rat_self_delimiting_code_zero : rat_self_delimiting_code 0 = [false, false, true, true, false] := by
  decide
