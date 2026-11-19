import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# is_bidirectional_ballot

Topic: combinatorics   Node: 51c6debe781d

Provenance: formalization of a published result. Source: arXiv:2611.23338, Definition 2.3

A finite set of integers $E$ is a bidirectional ballot set in $[0, h-1]$ if $E \subseteq [0, h-1]$ and for every integer $q \in [1, h]$, $q < 2 |E \cap [0, q-1]|$ and $q < 2 |E \cap [h-q, h-1]|$ (that is, both the prefix and suffix intersections of length $q$ have cardinality strictly greater than $q/2$).
-/

/-- A finite set of integers in [0, h-1] is a bidirectional ballot set if every nonempty prefix and suffix contains strictly more than half the elements. -/
def is_bidirectional_ballot (h : ℤ) (E : Finset ℤ) : Prop :=
  E ⊆ Finset.Icc 0 (h - 1) ∧
  ∀ q : ℤ, 1 ≤ q → q ≤ h →
    q < 2 * ((E ∩ Finset.Icc 0 (q - 1)).card : ℤ) ∧
    q < 2 * ((E ∩ Finset.Icc (h - q) (h - 1)).card : ℤ)
