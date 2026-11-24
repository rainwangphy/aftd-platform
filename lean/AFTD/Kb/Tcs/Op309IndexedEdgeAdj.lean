import AFTD.Prelude

/-!
# op309_indexed_edge_adj

Topic: graphs   Node: 5316a4a1c8b7

Provenance: helper lemma. OP-309 finite indexed-edge certificates

Two distinct indexed edges share an endpoint.
-/

def op309_indexed_edge_adj{n m : ℕ} (E : Fin n → Fin m × Fin m) (i j : Fin n) : Prop := i ≠ j ∧ ((E i).1 = (E j).1 ∨ (E i).1 = (E j).2 ∨
             (E i).2 = (E j).1 ∨ (E i).2 = (E j).2)
