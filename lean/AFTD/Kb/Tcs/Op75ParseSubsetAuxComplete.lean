import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseSubsetAux
import AFTD.Kb.Tcs.Op75ParseNatComplete
import AFTD.Kb.Tcs.Op75SubsetEncodingCons
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.ReluEncodeNat
import AFTD.Kb.Tcs.Op75ParseNat

/-!
# op75_parse_subset_aux_complete

Topic: np_completeness   Node: 9e404558d3a7

Provenance: helper lemma. OP-75: canonical subset-sum input decoder for the width-three ReLU compiler.

Sufficient fuel makes the parser accept every canonical instance and return its weights and target.
-/

theorem op75_parse_subset_aux_complete (as : List ℕ) (t : ℕ) (fuel : ℕ)
    (hf : as.length < fuel) :
    op75_parse_subset_aux fuel (op75_subset_encoding as t) = some (as, t) := by
  induction as generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
          have he := op75_parse_nat_complete t []
          simp only [List.append_nil] at he
          simp [op75_subset_encoding, op75_parse_subset_aux, he]
  | cons a as ih =>
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
          have hs : as.length < fuel := by simp at hf; omega
          rw [op75_subset_encoding_cons]
          simp only [op75_parse_subset_aux, op75_parse_nat_complete]
          rw [ih fuel hs]
