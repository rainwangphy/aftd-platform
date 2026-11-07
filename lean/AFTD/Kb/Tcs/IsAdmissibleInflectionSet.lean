import AFTD.Prelude
import AFTD.Kb.Tcs.PermInflectionSet

/-!
# is_admissible_inflection_set

Topic: combinatorics   Node: 4ceed8310cae

Provenance: formalization of a published result. Source: arXiv:2610.38237, Definition 3.1

A finite set I : Finset (ℕ × ℕ) is an admissible inflection set (is_admissible_inflection_set I) if there exist n : ℕ and a permutation σ : Equiv.Perm (Fin n) such that perm_inflection_set σ = I.
-/

/-- Predicate that a set of pairs is the inflection set of some permutation. -/
def is_admissible_inflection_set (I : Finset (ℕ × ℕ)) : Prop := ∃ (n : ℕ) (σ : Equiv.Perm (Fin n)), perm_inflection_set σ = I
