import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetCompilerSemantics
import AFTD.Kb.Tcs.KarpReducible
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.ReluNetwork3Encode
import AFTD.Kb.Tcs.Op75SubsetLanguage
import AFTD.Kb.Tcs.Op75CompactNetwork
import AFTD.Kb.Tcs.ReluWidth3UnitIntervalZeroLanguage

/-!
# op75_subset_compiler_correct_reduction

Topic: np_completeness   Node: 6e51415dcc71

Provenance: helper lemma. OP-75: separate the finite-machine compiler obligation from semantic correctness of the reduction.

A total polynomial-time Boolean compiler with the specified canonical output and a no-instance output on malformed words gives the desired Karp reduction.
-/

theorem op75_subset_compiler_correct_reduction (f : List Bool → List Bool)
    (hf : Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f))
    (hgood : ∀ (as : List ℕ) (t : ℕ),
      f (op75_subset_encoding as t) = relu_network3_encode (op75_compact_network as t))
    (hbad : ∀ w, (¬ ∃ as : List ℕ, ∃ t : ℕ, op75_subset_encoding as t = w) →
      f w ∉ relu_width3_unit_interval_zero_language) :
    KarpReducible Bool Bool op75_subset_language relu_width3_unit_interval_zero_language := by
  exact ⟨f, hf, op75_subset_compiler_semantics f hgood hbad⟩
