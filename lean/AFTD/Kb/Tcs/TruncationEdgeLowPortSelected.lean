import AFTD.Prelude

/-!
# truncation_edge_low_port_selected

Topic: graphs   Node: cc94b19c10f5

Provenance: helper lemma. Maximal unselected factor-path refinement for the OP-874 campaign.

An edge has at least one endpoint whose internal port uses its missing low color.
-/

def truncation_edge_low_port_selected {V : Type*} (G : SimpleGraph V)
    (b : V → Bool) (h : V → G.edgeSet → Fin 6) (u v : V) : Prop := ∃ e : G.edgeSet, (e : Sym2 V) = s(u,v) ∧
    (h u e = (if b u then 0 else 1) ∨ h v e = (if b v then 0 else 1))
