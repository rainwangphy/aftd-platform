import AFTD.Prelude

/-!
# bz3_cnt

Topic: general_equilibrium   Node: 19e87a494952

Pivot counts of the three players of a 3-player game given by its winning pattern on the eight coalitions.
-/

/-- Pivot counts of the three players of a 3-player game whose winning coalitions are encoded by `x k` for the coalition with bit pattern `k` (bit `j` set iff player `j` is in it). -/
def bz3_cnt (x : Fin 8 → Bool) : Fin 3 → ℕ :=
  ![(!x 0 && x 1).toNat + (!x 2 && x 3).toNat + (!x 4 && x 5).toNat + (!x 6 && x 7).toNat,
    (!x 0 && x 2).toNat + (!x 1 && x 3).toNat + (!x 4 && x 6).toNat + (!x 5 && x 7).toNat,
    (!x 0 && x 4).toNat + (!x 1 && x 5).toNat + (!x 2 && x 6).toNat + (!x 3 && x 7).toNat]
