import AFTD.Prelude

/-!
# bapat_sunder_coeffTable

Topic: combinatorics   Node: c7cfc1f2f0be

Provenance: helper lemma. step towards op_1992_real_bapat_sunder_counterexample_rank_two_or_three

The flat coefficient table of the product over the m columns of the linear forms (M 0 i) * X + (M 1 i) * Y + (M 2 i) * Z: entry number a * (m + 1) + b holds the coefficient of X^a * Y^b * Z^(t - a - b) after t columns have been multiplied. It is computed by a single left-to-right fold, so that kernel evaluation is linear time.
-/

/-- Computable flat (width `m+1`) coefficient table of `∏ i, (M 0 i * X + M 1 i * Y + M 2 i * Z)`. -/
def bapat_sunder_coeffTable {m : ℕ} (M : Matrix (Fin 3) (Fin m) ℤ) : List ℤ := ((List.finRange m).foldl
      (fun (p : List ℤ) (i : Fin m) =>
        List.zipWith3 (fun c y x => M 2 i * c + M 1 i * y + M 0 i * x)
          p (0 :: p) (List.replicate (m + 1) 0 ++ p))
      ((1 : ℤ) :: List.replicate ((m + 1) * (m + 1) - 1) 0))
