import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetCompilerFunctionCorrect
import AFTD.Kb.Tcs.KarpReducible
import AFTD.Kb.Tcs.ReluWidth3UnitIntervalZeroLanguage
import AFTD.Kb.Tcs.Op75SubsetLanguage
import AFTD.Kb.Tcs.Op75SubsetCompilerFunction

/-!
# op75_subset_compiler_machine_suffices

Topic: np_completeness   Node: e92d7df3659c

Provenance: helper lemma. OP-75: explicit total subset-sum to width-three network compiler.

If the explicit compiler is polynomial-time TM2 computable, the claimed subset-sum to network Karp reduction follows.
-/

theorem op75_subset_compiler_machine_suffices
    (h : Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) op75_subset_compiler_function)) :
    KarpReducible Bool Bool op75_subset_language relu_width3_unit_interval_zero_language := by
  exact ⟨op75_subset_compiler_function, h, op75_subset_compiler_function_correct⟩
