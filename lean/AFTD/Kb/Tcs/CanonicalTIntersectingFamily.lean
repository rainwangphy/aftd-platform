import AFTD.Prelude

/-!
# canonical_t_intersecting_family

Topic: combinatorics   Node: 27f4572c5989

Provenance: formalization of a published result. Source: arXiv:2611.25346 Sec. 1

The canonical t-intersecting family S_r^{\le k} consists of all subsets of [n] of size at most k containing at least t + r points from the first t + 2r elements.
-/

/-- The canonical t-intersecting family S_r^{\le k} of subsets of [n] of size at most k containing at least t+r points from the first t+2r elements. -/
def canonical_t_intersecting_family (n k t r : ℕ) : Finset (Finset (Fin n)) :=
  let base : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun x => (x : ℕ) < t + 2 * r)
  ((Finset.univ : Finset (Fin n)).powerset).filter (fun A =>
    A.card ≤ k ∧ t + r ≤ (A ∩ base).card)
