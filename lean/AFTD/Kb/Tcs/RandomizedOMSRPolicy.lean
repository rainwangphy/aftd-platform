import AFTD.Prelude
import AFTD.Kb.Tcs.OMSRArrival
import AFTD.Kb.Tcs.IsValidProbeSeq

/-!
# RandomizedOMSRPolicy

Topic: online_algorithms   Node: 3f5f277d366c

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:415

For n offline resources, a RandomizedOMSRPolicy packages a sample space Ω, a measurable space structure mΩ, a probability measure μ on Ω satisfying IsProbabilityMeasure μ, and a policy function policy : Ω → OMSRArrival n → Finset (Fin n) → List (Fin n) satisfying IsValidProbeSeq arr S (policy ω arr S) for all ω, arr, and S.
-/

/-- A randomized online matching policy with patience. -/
structure RandomizedOMSRPolicy (n : ℕ) where
  Ω : Type
  mΩ : MeasurableSpace Ω
  μ : MeasureTheory.Measure Ω
  hμ : MeasureTheory.IsProbabilityMeasure μ
  policy : Ω → OMSRArrival n → Finset (Fin n) → List (Fin n)
  valid : ∀ ω arr S, IsValidProbeSeq arr S (policy ω arr S)
