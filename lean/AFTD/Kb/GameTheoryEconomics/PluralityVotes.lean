import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# plurality_votes

Topic: social_choice   Node: 5901e493bd99

Provenance: formalization of a published result. Source: arXiv:2610.26535, Section 2.2

Given a preference profile prof assigning a linear order over candidates C to each voter in V, the plurality count of candidate c is the number of voters who rank c at the top.
-/

/-- The number of voters ranking candidate c first in an election profile. -/
noncomputable def plurality_votes {V C : Type*} [Fintype V]
    (prof : V → LinearOrder C) (c : C) : ℕ :=
  open Classical in
  (Finset.univ.filter (fun v => letI := prof v; IsTop c)).card
