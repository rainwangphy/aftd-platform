import AFTD.Prelude

/-!
# ranking_swap

Topic: fair_division   Node: 2597f6b0223e

Provenance: formalization of a published result. Source: arXiv:2610.23040 Definition 3.5

The ranking obtained from r by exchanging the goods in positions k and l.
-/

/-- The ranking obtained from `r` by exchanging the goods in positions `k` and `l` (a swap, Definition 3.5 of arXiv:2610.23040). -/
def ranking_swap {G : Type*} {m : ℕ} (r : Fin m ≃ G) (k l : Fin m) : Fin m ≃ G :=
  (Equiv.swap k l).trans r
