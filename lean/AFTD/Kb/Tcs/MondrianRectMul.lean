import AFTD.Prelude

/-!
# mondrian_rect_mul

Topic: combinatorics   Node: 8919aee19496

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Multiply all four rectangle coordinates by a.
-/

def mondrian_rect_mul (a : ℕ) (r : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (a * r.1, a * r.2.1, a * r.2.2.1, a * r.2.2.2)
