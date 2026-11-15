import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseNat

/-!
# op75_parse_subset_aux

Topic: np_completeness   Node: 6213891e29f9

Provenance: helper lemma. OP-75: canonical subset-sum input decoder for the width-three ReLU compiler.

A total fuel-bounded decoder for canonical subset-sum instances.
-/

def op75_parse_subset_aux : ℕ → List Bool → Option (List ℕ × ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, false :: tail =>
      match op75_parse_nat tail with
      | some (t, [], _) => some ([], t)
      | _ => none
  | fuel + 1, true :: tail =>
      match op75_parse_nat tail with
      | some (a, rest, _) =>
          match op75_parse_subset_aux fuel rest with
          | some (as, t) => some (a :: as, t)
          | none => none
      | none => none
