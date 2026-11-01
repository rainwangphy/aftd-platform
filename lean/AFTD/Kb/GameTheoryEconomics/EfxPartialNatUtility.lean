import AFTD.Prelude

/-!
# efx_partial_nat_utility

Topic: fair_division   Node: dfd9f0888e25

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

Natural utility in a partial allocation whose last owner label denotes unallocated goods.
-/

def efx_partial_nat_utility {n m : ℕ} (v : Fin n → Fin m → ℕ) (σ : Fin m → Fin (n+1)) (i : Fin n) : ℕ := ∑ g : Fin m, if σ g = i.castSucc then v i g else 0
