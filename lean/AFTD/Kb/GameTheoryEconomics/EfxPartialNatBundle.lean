import AFTD.Prelude

/-!
# efx_partial_nat_bundle

Topic: fair_division   Node: 9d0dba32e76f

Provenance: helper lemma. General partial EFX self-champion progress; related arXiv:2002.05119 Observation 6.

The goods held by an agent in a partial allocation, where the last owner label denotes unallocated goods.
-/

def efx_partial_nat_bundle {n m : ℕ} (σ : Fin m → Fin (n+1)) (i : Fin n) : Finset (Fin m) := Finset.univ.filter (fun g => σ g = i.castSucc)
