import AFTD.Prelude

/-!
# agSub

Topic: equilibria   Node: e3875278991e

Count vector seen by a player on strategy i when the totals are c.
-/

/-- Count vector seen by a player on strategy `i` when the totals are `c`. -/
def agSub {s : ℕ} (c : Fin s → ℕ) (i : Fin s) : Fin s → ℕ := fun k => c k - if k = i then 1 else 0
