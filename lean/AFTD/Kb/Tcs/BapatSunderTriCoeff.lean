import AFTD.Prelude
import AFTD.Kb.Tcs.BapatSunderFibreCount

/-!
# bapat_sunder_triCoeff

Topic: combinatorics   Node: efb08a732d3d

Provenance: helper lemma. step towards op_1992_real_bapat_sunder_counterexample_rank_two_or_three

For a 3 x m integer matrix M with columns v_i, the trinomial coefficient c(M,a,b,c) is the coefficient of X^a Y^b Z^c in the product over i of (M 0 i * X + M 1 i * Y + M 2 i * Z), written as the sum over phi : Fin m -> Fin 3 whose fibre counts are a, b, c of the product over i of M (phi i) i.
-/

/-- The coefficient of `X^a * Y^b * Z^c` in `∏ i, (M 0 i * X + M 1 i * Y + M 2 i * Z)`, as a sum over the maps whose fibre counts are `(a, b, c)`. -/
def bapat_sunder_triCoeff {m : ℕ} (M : Matrix (Fin 3) (Fin m) ℤ) (a b c : ℕ) : ℤ := ∑ φ : Fin m → Fin 3,
      if bapat_sunder_fibreCount φ 0 = a ∧ bapat_sunder_fibreCount φ 1 = b ∧
         bapat_sunder_fibreCount φ 2 = c then ∏ i, M (φ i) i else 0
