import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IndexedEdgeAdj
import AFTD.Kb.Tcs.Op309IndexedEdgeRich

/-!
# op309_indexed_rich_neighbor

Topic: graphs   Node: 310e8cb89a26

Provenance: helper lemma. OP-309 finite indexed-edge certificates

The indexed edge coloring is proper and every non-isolated edge has an adjacent rich edge.
-/

def op309_indexed_rich_neighbor{n m : ℕ} (E : Fin n → Fin m × Fin m) (C : Fin n → Fin 5) : Prop := (∀ i j, op309_indexed_edge_adj E i j → C i ≠ C j) ∧
  ∀ i, (∃ j, op309_indexed_edge_adj E i j) → ∃ j, op309_indexed_edge_adj E i j ∧ op309_indexed_edge_rich E C j
