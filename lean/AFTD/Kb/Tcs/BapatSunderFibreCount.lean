import AFTD.Prelude

/-!
# bapat_sunder_fibreCount

Topic: combinatorics   Node: dbd2034efb3b

Provenance: helper lemma. step towards op_1992_real_bapat_sunder_counterexample_rank_two_or_three

For a function phi : Fin m -> Fin 3 and a value k : Fin 3, the fibre count of phi at k is the number of indices i with phi i = k.
-/

/-- The number of indices at which a map `Fin m → Fin 3` takes the value `k`. -/
def bapat_sunder_fibreCount {m : ℕ} (φ : Fin m → Fin 3) (k : Fin 3) : ℕ := (Finset.univ.filter (fun i => φ i = k)).card
