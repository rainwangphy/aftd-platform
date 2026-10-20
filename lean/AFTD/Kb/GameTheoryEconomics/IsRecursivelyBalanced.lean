import AFTD.Prelude

/-!
# is_recursively_balanced

Topic: fair_division   Node: 40070fe05d3c

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 2

A picking sequence of length m for n agents is recursively balanced if each complete round of n turns contains every agent exactly once and any final incomplete round contains no agent more than once.
-/

/-- A picking sequence of length m for n agents is recursively balanced if every complete round of n turns is a permutation of the agents and the final incomplete round has no repeated agents. -/
def is_recursively_balanced (n : ℕ) (seq : List (Fin n)) : Prop :=
  ∀ s : ℕ, ((seq.drop (s * n)).take n).Nodup
