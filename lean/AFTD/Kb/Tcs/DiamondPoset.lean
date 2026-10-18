import AFTD.Prelude

/-!
# DiamondPoset

Topic: combinatorics   Node: 33182d7b892c

Provenance: formalization of a published result. Source: arXiv:2610.20545, The k-color poset Ramsey number of the diamond is 2k

For a natural number j, DiamondPoset j is the type consisting of a bottom element bot, a top element top, and j middle elements indexed by Fin j.
-/

/-- The j-diamond poset with a minimum, a maximum, and an antichain of j middle elements. -/
inductive DiamondPoset (j : ℕ) : Type | bot : DiamondPoset j
  | mid : Fin j → DiamondPoset j
  | top : DiamondPoset j
  deriving DecidableEq, Fintype
