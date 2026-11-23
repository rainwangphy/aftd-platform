import AFTD.Prelude
import AFTD.Kb.Tcs.RatSelfDelimitingCode

/-!
# rat_self_delimiting_code_neg_half

Topic: approximation   Node: 98e2ecf44ddf

Provenance: helper lemma. Sanity check of rat_self_delimiting_code.

The code of -1/2: sign true, numerator 1 as true,true,false, denominator 2 as true,false,true,true,false.
-/

theorem rat_self_delimiting_code_neg_half :
    rat_self_delimiting_code (-1/2) = [true, true, true, false, true, false, true, true, false] := by
  decide +kernel
