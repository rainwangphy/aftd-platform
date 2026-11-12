import AFTD.Prelude
import AFTD.Kb.Tcs.InstFintypeOrderHom
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# dedekind_number

Topic: combinatorics   Node: 154940c7e72d

Provenance: formalization of a published result. Source: arXiv:2611.13887 Section 1

The n-th Dedekind number d_n is the number of monotone Boolean functions on n variables, defined as the cardinality of the poset of monotone functions from {0, 1}^n to {0, 1}.
-/

/-- The n-th Dedekind number, the cardinality of the poset of monotone Boolean functions on n variables. -/
noncomputable def dedekind_number (n : ℕ) : ℕ := Fintype.card ((Fin n → Bool) →o Bool)
