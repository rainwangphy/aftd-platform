import AFTD.Prelude

/-!
# binary_rank

Topic: streaming   Node: b90b717ea911

Provenance: formalization of a published result. Source: arXiv:2611.14163, Definition 2.1

For an n × m binary matrix H with entries in Fin 2, the binary rank is the infimum in ℕ of all natural numbers k for which there exist binary matrices A : Matrix (Fin n) (Fin k) (Fin 2) and B : Matrix (Fin k) (Fin m) (Fin 2) whose values in ℕ satisfy H.map (·.val) = A.map (·.val) * B.map (·.val).
-/

/-- The binary rank of a binary matrix H is the minimum inner dimension k of a binary factorization H = A * B over ℕ. -/
noncomputable def binary_rank {n m : ℕ} (H : Matrix (Fin n) (Fin m) (Fin 2)) : ℕ := sInf {k : ℕ | ∃ (A : Matrix (Fin n) (Fin k) (Fin 2)) (B : Matrix (Fin k) (Fin m) (Fin 2)),
    H.map (·.val) = A.map (·.val) * B.map (·.val)}
