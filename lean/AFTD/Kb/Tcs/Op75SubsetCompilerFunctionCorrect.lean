import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetCompilerFunction
import AFTD.Kb.Tcs.Op75SubsetCompilerSemantics
import AFTD.Kb.Tcs.Op75ParseSubsetSpec
import AFTD.Kb.Tcs.Op75InvalidInputFallbackNonmember
import AFTD.Kb.Tcs.ReluWidth3UnitIntervalZeroLanguage
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.Op75ParseSubset
import AFTD.Kb.Tcs.ReluNetwork3Encode
import AFTD.Kb.Tcs.Op75SubsetLanguage
import AFTD.Kb.Tcs.Op75CompactNetwork

/-!
# op75_subset_compiler_function_correct

Topic: np_completeness   Node: 96fe5c0f21a7

Provenance: helper lemma. OP-75: explicit total subset-sum to width-three network compiler.

The explicit total compiler preserves language membership.
-/

theorem op75_subset_compiler_function_correct (w : List Bool) :
    w ∈ op75_subset_language ↔ op75_subset_compiler_function w ∈ relu_width3_unit_interval_zero_language := by
  apply op75_subset_compiler_semantics op75_subset_compiler_function
  · intro as t
    have hp := (op75_parse_subset_spec (op75_subset_encoding as t) as t).2 rfl
    simp [op75_subset_compiler_function, hp]
  · intro w hbad
    cases hp : op75_parse_subset w with
    | none => simpa [op75_subset_compiler_function, hp] using op75_invalid_input_fallback_nonmember
    | some value =>
        rcases value with ⟨as, t⟩
        have he := (op75_parse_subset_spec w as t).1 hp
        exact False.elim (hbad ⟨as,t,he⟩)
