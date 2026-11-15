import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseNatSound
import AFTD.Kb.Tcs.Op75ParseNatComplete
import AFTD.Kb.Tcs.Op75ParseNat
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_parse_nat_spec

Topic: np_completeness   Node: e1ac341f982d

Provenance: helper lemma. OP-75: canonical binary natural parser for the subset-sum-to-network compiler.

A successful natural parse is equivalent to the input being its canonical value encoding followed by the returned suffix, with the correct nonzero flag.
-/

theorem op75_parse_nat_spec (w : List Bool) (n : ℕ) (rest : List Bool) (nz : Bool) :
    op75_parse_nat w = some (n, rest, nz) ↔
      w = relu_encode_nat n ++ rest ∧ nz = decide (n ≠ 0) := by
  constructor
  · exact op75_parse_nat_sound w n rest nz
  · rintro ⟨rfl,rfl⟩
    exact op75_parse_nat_complete n rest
