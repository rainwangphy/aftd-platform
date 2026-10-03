import AFTD.Prelude

/-!
# bz3_coal

Topic: general_equilibrium   Node: 443664556d5c

The eight coalitions of three players indexed by bit pattern.
-/

/-- The eight coalitions of three players, indexed by bit pattern (bit `j` set iff player `j` is in). -/
def bz3_coal : Fin 8 → Finset (Fin 3) :=
  ![∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}]
