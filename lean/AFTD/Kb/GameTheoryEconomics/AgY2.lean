import AFTD.Prelude

/-!
# agY2

Topic: equilibria   Node: 541bbc4907ae

Two-strategy count vector with k others on strategy 1.
-/

/-- Two-strategy count vector with `k` others on strategy `1`. -/
def agY2 (n k : ℕ) : Fin 2 → ℕ := fun j => if j = 1 then k else n - 1 - k
