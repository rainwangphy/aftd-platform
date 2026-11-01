import AFTD.Prelude

/-!
# efx_pareto_lock_padded_owner

Topic: fair_division   Node: 3f8f39c1830d

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

Use the original partial allocation, assigning the first k added goods to source 0 and the other k to source 1.
-/

def efx_pareto_lock_padded_owner (k : ℕ) : Fin (8+(k+k)) → Fin 5 := Fin.addCases ![(1 : Fin 5),0,0,0,1,2,4,3] (fun g : Fin (k+k) => if (g : ℕ) < k then 0 else 1)
