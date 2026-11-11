import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup
import AFTD.Kb.Tcs.NumericalSemigroupFrobeniusNumber
import AFTD.Kb.Tcs.NumericalSemigroupMultiplicity
import AFTD.Kb.Tcs.NumericalSemigroupGenus

/-!
# numerical_semigroup_count

Topic: combinatorics   Node: 775d9e88896a

Provenance: formalization of a published result. Source: arXiv:2611.11559 Section 2

The counting function n_{F,m,g} of numerical semigroups, defined as the number (cardinality) of numerical semigroups with Frobenius number F, multiplicity m, and genus g.
-/

/-- The number of numerical semigroups with Frobenius number F, multiplicity m, and genus g. -/
noncomputable def numerical_semigroup_count (F m g : ℕ) : ℕ := {S : NumericalSemigroup |
    numerical_semigroup_frobenius_number S = F ∧
    numerical_semigroup_multiplicity S = m ∧
    numerical_semigroup_genus S = g}.ncard
