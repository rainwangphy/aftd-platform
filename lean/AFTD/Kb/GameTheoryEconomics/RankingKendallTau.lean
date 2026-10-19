import AFTD.Prelude

/-!
# ranking_kendall_tau

Topic: fair_division   Node: 3e9fc6465b6c

Provenance: formalization of a published result. Source: arXiv:2610.23040 proof of Theorem 3.12 (the Kendall tau distance between the two agents' bids)

The Kendall tau distance between two strict rankings r and s of the goods: the number of ordered pairs (g, h) that r ranks g above h while s ranks h above g.
-/

/-- The Kendall tau distance between two strict rankings: the number of pairs of goods the two rankings order differently. -/
def ranking_kendall_tau {G : Type*} [Fintype G] [DecidableEq G] {m : ℕ} (r s : Fin m ≃ G) : ℕ :=
  ((Finset.univ : Finset (G × G)).filter
    (fun p => r.symm p.1 < r.symm p.2 ∧ s.symm p.2 < s.symm p.1)).card
