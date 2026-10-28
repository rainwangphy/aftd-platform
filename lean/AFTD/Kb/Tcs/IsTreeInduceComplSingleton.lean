import AFTD.Prelude

/-!
# is_tree_induce_compl_singleton

Topic: graphs   Node: cb08ed9c0874

Provenance: helper lemma. step towards is_tree_card_coloring_three

Removing a vertex of degree one from a finite tree yields an induced subgraph that is also a tree.
-/

/-- Removing a vertex of degree one from a finite tree yields an induced subgraph that is also a tree. -/
lemma is_tree_induce_compl_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {v : V} (hv : T.degree v = 1) :
    (T.induce {v}ᶜ).IsTree := ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv, hT.isAcyclic.induce {v}ᶜ⟩
