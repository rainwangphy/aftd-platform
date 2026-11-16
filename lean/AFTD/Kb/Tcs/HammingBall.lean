import AFTD.Prelude

/-!
# hamming_ball

Topic: information   Node: 08ab93fc30b5

Provenance: formalization of a published result. Source: arXiv:2611.18156 Section II

Given implicit parameters n and q, the Hamming ball `hamming_ball r x` of radius r centered at x : Fin n → Fin q is the finite set (Finset) of all y : Fin n → Fin q with hammingDist x y ≤ r.
-/

/-- The Hamming ball of radius r centered at x in (Fin n → Fin q), as a Finset. -/
def hamming_ball {n q : ℕ} (r : ℕ) (x : Fin n → Fin q) : Finset (Fin n → Fin q) :=
  Finset.filter (fun y => hammingDist x y ≤ r) Finset.univ
