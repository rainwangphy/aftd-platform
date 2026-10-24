import AFTD.Prelude
import AFTD.Kb.Tcs.IsTwoFourCode

/-!
# two_four_code_max_card

Topic: information   Node: b7f8c950ece9

Provenance: formalization of a published result. Source: arXiv:2610.30613, Section 1, eq. (1)

For integers $q$ and $n$, $A_q(n, \{2,4\})$ is the supremum of cardinalities of finite subsets of $\mathrm{Fin}\, n \to \mathrm{Fin}\, q$ that are $\{2, 4\}$-codes.
-/

/-- A_q(n, {2,4}): the maximum cardinality of a {2,4}-distance code of length n over an alphabet of size q. -/
noncomputable def two_four_code_max_card (q n : ℕ) : ℕ := sSup { k : ℕ | ∃ s : Finset (Fin n → Fin q), s.card = k ∧ is_two_four_code (↑s : Set (Fin n → Fin q)) }
