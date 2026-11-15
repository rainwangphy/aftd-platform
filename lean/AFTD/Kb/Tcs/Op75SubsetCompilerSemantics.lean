import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetLanguage
import AFTD.Kb.Tcs.Op75CompactNetworkSubsetSum
import AFTD.Kb.Tcs.ReluWidth3LanguageMemIff
import AFTD.Kb.Tcs.ReluNetwork3Encode
import AFTD.Kb.Tcs.Op75Subset
import AFTD.Kb.Tcs.ReluWidth3UnitIntervalZeroLanguage
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.Op75CompactNetwork
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero

/-!
# op75_subset_compiler_semantics

Topic: np_completeness   Node: 800072771140

Provenance: helper lemma. OP-75: semantic correctness for the subset-sum to width-three ReLU network reduction.

Any total binary function that maps canonical subset-sum instances to their specified networks and maps malformed inputs outside the zero language preserves membership in both directions. The result does not assume encoding injectivity or polynomial-time computability.
-/

theorem op75_subset_compiler_semantics (f : List Bool → List Bool)
    (hgood : ∀ (as : List ℕ) (t : ℕ),
      f (op75_subset_encoding as t) = relu_network3_encode (op75_compact_network as t))
    (hbad : ∀ w, (¬ ∃ as : List ℕ, ∃ t : ℕ, op75_subset_encoding as t = w) →
      f w ∉ relu_width3_unit_interval_zero_language) :
    ∀ w, w ∈ op75_subset_language ↔ f w ∈ relu_width3_unit_interval_zero_language := by
  intro w
  constructor
  · rintro ⟨as, t, rfl, hs⟩
    rw [hgood, relu_width3_language_mem_iff, op75_compact_network_subset_sum]
    exact hs
  · intro hw
    by_cases hc : ∃ as : List ℕ, ∃ t : ℕ, op75_subset_encoding as t = w
    · obtain ⟨as, t, he⟩ := hc
      refine ⟨as, t, he, ?_⟩
      rw [← he, hgood, relu_width3_language_mem_iff, op75_compact_network_subset_sum] at hw
      exact hw
    · exact False.elim (hbad w hc hw)
