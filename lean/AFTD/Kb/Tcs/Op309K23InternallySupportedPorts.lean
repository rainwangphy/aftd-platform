import AFTD.Prelude

/-!
# op309_k23_internally_supported_ports

Topic: graphs   Node: c17a0a553eaf

Provenance: helper lemma. OP-309 bridgeless network counting.

Ports incident to a selected edge whose other endpoint lies in the same five-vertex block.
-/

def op309_k23_internally_supported_ports {I : Type*} [Fintype I] [DecidableEq I]
  (G : SimpleGraph (I × Fin 5)) [DecidableRel G.Adj] (R : Finset G.edgeSet) : Finset (I × Fin 5) := Finset.univ.filter fun x => 2 ≤ x.2.val ∧
  ∃ q : Fin 5, q ≠ x.2 ∧ ∃ e ∈ R, x ∈ e.1 ∧ (x.1,q) ∈ e.1
