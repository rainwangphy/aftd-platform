import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissibleInflectionSet
import AFTD.Kb.Tcs.PermInflectionSet

/-!
# is_vanishing_inflection_set

Topic: combinatorics   Node: b98ba3fe9502

Provenance: formalization of a published result. Source: arXiv:2610.38237, Definition 3.1

A finite set I : Finset (ℕ × ℕ) is a vanishing inflection set (is_vanishing_inflection_set I) if is_admissible_inflection_set I holds and the set {n : ℕ | ∃ σ : Equiv.Perm (Fin n), perm_inflection_set σ = I} is finite.
-/

/-- Predicate that an admissible inflection set has witnesses in Sym_n for only finitely many n. -/
def is_vanishing_inflection_set (I : Finset (ℕ × ℕ)) : Prop := is_admissible_inflection_set I ∧
  {n : ℕ | ∃ σ : Equiv.Perm (Fin n), perm_inflection_set σ = I}.Finite
