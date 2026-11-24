import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IndexedEdgeAdj

/-!
# op309_indexed_edge_rich

Topic: graphs   Node: 3e53b788ca61

Provenance: helper lemma. OP-309 finite indexed-edge certificates

Every two distinct edges adjacent to the indexed edge receive distinct colors.
-/

def op309_indexed_edge_rich{n m : ℕ} (E : Fin n → Fin m × Fin m) (C : Fin n → Fin 5) (i : Fin n) : Prop := ∀ j k, op309_indexed_edge_adj E i j → op309_indexed_edge_adj E i k → j ≠ k → C j ≠ C k
