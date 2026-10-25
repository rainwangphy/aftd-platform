import AFTD.Prelude

/-!
# stabilizer_campbell_howard_conditions

Topic: quantum   Node: ac3a6545654c

Provenance: formalization of a published result. Source: arXiv:2610.09341 Table 1

An s by n matrix S over ZMod 2 satisfies the stabilizer-only Campbell-Howard conditions S1, S2, S3 if its rows have even Hamming weight (S1), even pairwise overlap (S2), and even triple overlap (S3).
-/

/-- The stabilizer-only Campbell-Howard conditions S1, S2, S3 for an s by n binary matrix. -/
def stabilizer_campbell_howard_conditions {s n : ℕ}
    (S : Matrix (Fin s) (Fin n) (ZMod 2)) : Prop :=
  (∀ l : Fin s, ∑ j : Fin n, S l j = 0) ∧
  (∀ l l' : Fin s, l < l' → ∑ j : Fin n, S l j * S l' j = 0) ∧
  (∀ l l' l'' : Fin s, l < l' → l' < l'' → ∑ j : Fin n, S l j * S l' j * S l'' j = 0)
