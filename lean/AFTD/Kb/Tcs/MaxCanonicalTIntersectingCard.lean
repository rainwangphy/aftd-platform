import AFTD.Prelude

/-!
# max_canonical_t_intersecting_card

Topic: combinatorics   Node: 9f6cd679ddc7

Provenance: formalization of a published result. Source: arXiv:2611.25346 Theorem 1.4

The maximum cardinality max_{0 ≤ r ≤ ⌊(n-t)/2⌋} |S_r^{\le k}| of the canonical t-intersecting families.
-/

/-- The maximum cardinality of the canonical t-intersecting families S_r^{\le k} for 0 ≤ r ≤ (n-t)/2. -/
def max_canonical_t_intersecting_card (n k t : ℕ) : ℕ :=
  (Finset.range ((n - t) / 2 + 1)).sup (fun r =>
    let base : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun x => (x : ℕ) < t + 2 * r)
    let fam : Finset (Finset (Fin n)) := ((Finset.univ : Finset (Fin n)).powerset).filter (fun A =>
      A.card ≤ k ∧ t + r ≤ (A ∩ base).card)
    fam.card)
