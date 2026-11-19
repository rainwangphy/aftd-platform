import AFTD.Prelude

/-!
# op309_bit_matching_witness

Topic: graphs   Node: c9c9ae35444f

Provenance: helper lemma. Boolean reduction of the cubic matching-recoloring route to OP-309.

A Boolean matching witness consists of a matching M and two Boolean edge labels b,d such that every vertex sees both first labels, adjacent edges with the same first label have different second labels, and every edge has an adjacent edge uv from an M-uncovered vertex u to an M-covered vertex v whose other nonmatching edge j has the first label of the unique minority-first edge k at u and the opposite second label.
-/

def op309_bit_matching_witness {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (b d : G.edgeSet → Bool) (M : Finset G.edgeSet) : Prop :=
    let covered : V → Prop := fun v => ∃ f ∈ M, v ∈ f.1
    (∀ f ∈ M, ∀ g ∈ M, f ≠ g → ¬ G.lineGraph.Adj f g) ∧
    (∀ v : V, ∃ f g : G.edgeSet, v ∈ f.1 ∧ v ∈ g.1 ∧ b f ≠ b g) ∧
    (∀ f g : G.edgeSet, G.lineGraph.Adj f g → b f = b g → d f ≠ d g) ∧
    (∀ e : G.edgeSet, ∃ f : G.edgeSet, G.lineGraph.Adj e f ∧
      ∃ u v : V, ∃ j k : G.edgeSet,
        f.1 = s(u,v) ∧ ¬ covered u ∧ covered v ∧
        v ∈ j.1 ∧ j ≠ f ∧ j ∉ M ∧ u ∈ k.1 ∧
        (∀ h : G.edgeSet, u ∈ h.1 → h ≠ k → b h ≠ b k) ∧
        b j = b k ∧ d j ≠ d k)
