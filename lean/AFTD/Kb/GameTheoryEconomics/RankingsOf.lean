import AFTD.Prelude

/-!
# rankings_of

Topic: social_choice   Node: 33e10146514a

The rankings of a finite set S of alternatives: all orderings of S as duplicate-free lists.
-/

/-- The rankings of a finite set `S` of alternatives: all orderings of `S` as lists. -/
noncomputable def rankings_of (S : Finset ℕ) : Finset (List ℕ) :=
  S.toList.permutations.toFinset
