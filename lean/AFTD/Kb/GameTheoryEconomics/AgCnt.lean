import AFTD.Prelude

/-!
# agCnt

Topic: equilibria   Node: f1af51c2ccff

Number of players other than p using strategy j in the pure profile σ.
-/

open Finset in
/-- Number of players other than `p` using strategy `j` in the pure profile `σ`. -/
def agCnt {n s : ℕ} (σ : Fin n → Fin s) (p : Fin n) (j : Fin s) : ℕ :=
  (Finset.univ.filter (fun q => q ≠ p ∧ σ q = j)).card
