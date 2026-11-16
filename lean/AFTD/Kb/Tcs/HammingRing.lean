import AFTD.Prelude

/-!
# hamming_ring

Topic: information   Node: a56a0e064fd2

Provenance: formalization of a published result. Source: arXiv:2611.18156 Definition III.1

Given implicit parameters n and q, the (c, c') Hamming ring `hamming_ring c c' x` centered at x : Fin n → Fin q is the finite set (Finset) of all y : Fin n → Fin q satisfying c + 1 ≤ hammingDist x y ∧ hammingDist x y ≤ c + c'.
-/

/-- The (c, c') Hamming ring centered at x in (Fin n → Fin q), as a Finset. -/
def hamming_ring {n q : ℕ} (c c' : ℕ) (x : Fin n → Fin q) : Finset (Fin n → Fin q) :=
  Finset.filter (fun y => c + 1 ≤ hammingDist x y ∧ hammingDist x y ≤ c + c') Finset.univ
