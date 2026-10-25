import AFTD.Prelude

/-!
# is_perm_cover

Topic: automata   Node: e21748a4b93b

Provenance: formalization of a published result. Source: arXiv:2610.11098, Definition 3.2

For a natural number k and a finite set C of natural numbers, is_perm_cover k C holds if every d in C is strictly positive (0 < d), and for every permutation σ of Fin k, there exists d in C such that the order of σ divides d.
-/

/-- A finite set C of natural numbers covers the element orders of Equiv.Perm (Fin k) if all elements are positive and every order divides some d ∈ C. -/
def is_perm_cover (k : ℕ) (C : Finset ℕ) : Prop := (∀ d ∈ C, 0 < d) ∧ ∀ σ : Equiv.Perm (Fin k), ∃ d ∈ C, orderOf σ ∣ d
