import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# gnd_partial_load

Topic: online_algorithms   Node: d03ff12ba98b

Provenance: formalization of a published result. Source: arXiv:2611.30912 Section 2

For a sequence of N requests, the online load on resource e immediately prior to processing request i is the sum of weights w j e over prior requests j < i where e ∈ reply j.
-/

/-- Partial load on each resource from requests prior to request i. -/
noncomputable def gnd_partial_load {E : Type*} [DecidableEq E] {N : ℕ} (reply : Fin N → Finset E) (w : Fin N → E → ℝ) (i : Fin N) : E → ℝ := fun e => ∑ j ∈ Finset.Iio i, if e ∈ reply j then w j e else 0
