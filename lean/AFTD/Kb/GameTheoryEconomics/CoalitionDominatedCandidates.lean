import AFTD.Prelude

/-!
# coalition_dominated_candidates

Topic: social_choice   Node: 8f31ebdc2db9

Provenance: formalization of a published result. Source: arXiv:2610.26535, Section 2.2

For finite candidate type C with decidable equality, voter type V, an election profile prof : V → LinearOrder C, a candidate a : C, and a finite set of voters S : Finset V, coalition_dominated_candidates prof a S is the Finset of candidates c in C such that there exists some voter v in S for whom (prof v).le c a.
-/

/-- The set of candidates ranked weakly below candidate a by at least one voter in coalition S. -/
def coalition_dominated_candidates {V C : Type*} [Fintype C] [DecidableEq C]
    (prof : V → LinearOrder C) (a : C) (S : Finset V) : Finset C :=
  S.biUnion (fun v => Finset.univ.filter (fun c => (prof v).le c a))
