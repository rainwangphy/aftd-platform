import AFTD.Prelude

/-!
# round_robin_sequence

Topic: fair_division   Node: a56ca0423322

Provenance: formalization of a published result. Source: arXiv:2610.23040 (On the Convergence of Iterated Round Robin), Sec. 2; also arXiv:2610.23686 Sec. 2

The Round-Robin picking sequence (1, 2, ..., n, 1, 2, ...) of length m, with agents numbered 0, ..., n-1.
-/

/-- The Round-Robin picking sequence `(0, 1, ..., n-1, 0, 1, ...)` of length `m`. -/
def round_robin_sequence (n m : ℕ) [NeZero n] : List (Fin n) :=
  List.ofFn (fun t : Fin m => (⟨t.val % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩ : Fin n))
