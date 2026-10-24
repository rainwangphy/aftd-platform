import AFTD.Prelude
import AFTD.Kb.Tcs.HashPotential

/-!
# hash_potential_delta

Topic: data_structures   Node: b476c96e91c6

Provenance: formalization of a published result. Source: arXiv:2610.31363 Section 4

For a table of size n, offset sequence r, slot subset S, target sequence length t, prefix A, and next element e, the step change hash_potential_delta n r S t A e is the difference in potential hash_potential n r S t (A ++ [e]) - hash_potential n r S t A.
-/

/-- Step change in potential delta(A, e) = phi(A ++ [e]) - phi(A). -/
noncomputable def hash_potential_delta (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (S : Finset (ZMod n)) (t : ℕ) (A : List (ZMod n)) (e : ZMod n) : ℝ :=
  hash_potential n r S t (A ++ [e]) - hash_potential n r S t A
