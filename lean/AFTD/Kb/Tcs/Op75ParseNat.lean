import AFTD.Prelude

/-!
# op75_parse_nat

Topic: np_completeness   Node: 951b35f16fcd

Provenance: helper lemma. OP-75: canonical binary natural parser for the subset-sum-to-network compiler.

Decode one canonical self-delimiting binary natural, returning its value, the unconsumed suffix, and whether the value is nonzero; reject malformed or noncanonical encodings.
-/

def op75_parse_nat : List Bool → Option (ℕ × List Bool × Bool)
  | [] => none
  | false :: tail => some (0, tail, false)
  | true :: [] => none
  | true :: bit :: tail =>
      match op75_parse_nat tail with
      | none => none
      | some (n, rest, nz) =>
          if nz || bit then some (bit.toNat + 2*n, rest, true) else none
