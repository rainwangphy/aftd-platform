import AFTD.Prelude

/-!
# hunger_max_norm

Topic: combinatorial_games   Node: b8c865cddf23

Provenance: formalization of a published result. Source: arXiv:2610.08949

The maximum absolute value of coordinates of a rational hunger vector h.
-/

/-- The infinity norm (maximum absolute value) of a rational vector. -/
def hunger_max_norm {n : ℕ} (h : Fin n → ℚ) : ℚ := Finset.fold max (0 : ℚ) (fun i => |h i|) Finset.univ
