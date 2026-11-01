import AFTD.Prelude

/-!
# efx_partial_scaled_tail

Topic: fair_division   Node: a06991925f90

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

Scale each natural base value by K and append arbitrary natural-valued tail goods.
-/

def efx_partial_scaled_tail {n m k : ℕ} (K : ℕ) (v : Fin n → Fin m → ℕ) (d : Fin n → Fin k → ℕ) : Fin n → Fin (m+k) → ℕ := fun i => Fin.addCases (fun g => K * v i g) (d i)
