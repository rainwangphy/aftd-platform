import AFTD.Prelude

/-!
# fse_mix

Topic: mechanism_design   Node: c445c28ce42e

Profiles obtained from c by replacing the first k coordinates with those of z.
-/

/-- Profiles obtained from `c` by replacing the first `k` coordinates with those of `z`. -/
def fse_mix {n : ℕ} (c z : Fin n → ℝ) (k : ℕ) : Fin n → ℝ := fun j => if j.val < k then z j else c j
