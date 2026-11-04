import AFTD.Prelude

/-!
# two_insertion_collision_defect_envelope

Topic: information   Node: 82a2d65a0535

Provenance: original. Related work: arXiv:2611.01064 Maximal input entropy for binary two-deletion and two-insertion channels

For a natural number n, two_insertion_collision_defect_envelope n is n.choose 2 plus the minimum over all k in the defect set K_n of the cost 2 * k * n + 2 * k^2 + n - 10 * k - 2 + (k + 1 - r) * q^2 + r * (q + 1)^2, where K_n is the union of {1} and all integers k with 2 ≤ k ≤ (n - 2) / 3 - 1, and q = (n - 2) / (k + 1) and r = (n - 2) % (k + 1).
-/

/-- The exact balanced defect collision envelope for two insertions in a binary word of length n. -/
def two_insertion_collision_defect_envelope (n : ℕ) : ℕ := let K : Finset ℕ := insert 1 (Finset.Icc 2 ((n - 2) / 3 - 1))
  n.choose 2 + (K.image (fun k =>
    let q := (n - 2) / (k + 1)
    let r := (n - 2) % (k + 1)
    2 * k * n + 2 * k ^ 2 + n - 10 * k - 2 + (k + 1 - r) * q ^ 2 + r * (q + 1) ^ 2)).min'
    (Finset.Nonempty.image ⟨1, Finset.mem_insert_self 1 _⟩ _)
