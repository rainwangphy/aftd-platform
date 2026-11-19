import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_short_rich_paths

Topic: graphs   Node: c28d0e54d854

Provenance: helper lemma. Short-path formulation of the cubic rich-neighbor route for OP-309, supported by experiments 33425, 33446 and 33447.

A set of rich edges is a short rich path system when its components are vertex-disjoint paths with at most three edges; isolated selected edges are allowed for boundary constructions.
-/

def op309_short_rich_paths {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (c : G.lineGraph.Coloring (Fin 5)) (R : Finset G.edgeSet) : Prop :=
    (∀ f ∈ R, simple_graph_edge_is_rich G c f) ∧
    (∀ v : V, (R.filter fun e => v ∈ e.1).card ≤ 2) ∧
    (∀ a b d : V, [a,b,d].Nodup →
      ¬ (s(a,b) ∈ R.image Subtype.val ∧ s(b,d) ∈ R.image Subtype.val ∧
         s(d,a) ∈ R.image Subtype.val)) ∧
    (∀ a b d e : V, [a,b,d,e].Nodup →
      ¬ (s(a,b) ∈ R.image Subtype.val ∧ s(b,d) ∈ R.image Subtype.val ∧
         s(d,e) ∈ R.image Subtype.val ∧ s(e,a) ∈ R.image Subtype.val)) ∧
    (∀ a b d e f : V, [a,b,d,e,f].Nodup →
      ¬ (s(a,b) ∈ R.image Subtype.val ∧ s(b,d) ∈ R.image Subtype.val ∧
         s(d,e) ∈ R.image Subtype.val ∧ s(e,f) ∈ R.image Subtype.val))
