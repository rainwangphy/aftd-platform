import AFTD.Prelude

/-!
# campbell_howard_conditions

Topic: quantum   Node: 93dbce9afacd

Provenance: formalization of a published result. Source: arXiv:2610.09341 Table 1

The nine Campbell-Howard conditions for a logical X-matrix K of 3 rows and an X-stabilizer matrix S of s rows over ZMod 2: the logical rows have even weight (K1), even pairwise overlap (K2), and odd triple overlap (K3); logical and stabilizer rows have even pairwise overlap (KS1) and even triple overlaps (KS2, KS3); and stabilizer rows have even weight (S1), even pairwise overlap (S2), and even triple overlap (S3).
-/

/-- The nine Campbell-Howard conditions on logical and stabilizer rows for quasi-transversal CCZ on a CSS code. -/
def campbell_howard_conditions {s n : ℕ}
    (K : Matrix (Fin 3) (Fin n) (ZMod 2)) (S : Matrix (Fin s) (Fin n) (ZMod 2)) : Prop :=
  (∀ i : Fin 3, ∑ j : Fin n, K i j = 0) ∧
  (∀ i i' : Fin 3, i < i' → ∑ j : Fin n, K i j * K i' j = 0) ∧
  ((∑ j : Fin n, K 0 j * K 1 j * K 2 j) = 1) ∧
  (∀ (i : Fin 3) (l : Fin s), ∑ j : Fin n, K i j * S l j = 0) ∧
  (∀ (i i' : Fin 3) (l : Fin s), i < i' → ∑ j : Fin n, K i j * K i' j * S l j = 0) ∧
  (∀ (i : Fin 3) (l l' : Fin s), l < l' → ∑ j : Fin n, K i j * S l j * S l' j = 0) ∧
  (∀ l : Fin s, ∑ j : Fin n, S l j = 0) ∧
  (∀ l l' : Fin s, l < l' → ∑ j : Fin n, S l j * S l' j = 0) ∧
  (∀ l l' l'' : Fin s, l < l' → l' < l'' → ∑ j : Fin n, S l j * S l' j * S l'' j = 0)
