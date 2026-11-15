import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseSubset
import AFTD.Kb.Tcs.Op75CompactNetwork
import AFTD.Kb.Tcs.ReluNetwork3Encode

/-!
# op75_subset_compiler_function

Topic: np_completeness   Node: 706b5006a25b

Provenance: helper lemma. OP-75: explicit total subset-sum to width-three network compiler.

Compile a canonical subset-sum input to the explicit width-three network encoding; map malformed input to the fixed no-instance.
-/

def op75_subset_compiler_function (w : List Bool) : List Bool :=
  match op75_parse_subset w with
  | some (as, t) => relu_network3_encode (op75_compact_network as t)
  | none => relu_network3_encode (op75_compact_network [] 1)
