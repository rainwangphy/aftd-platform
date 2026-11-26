import AFTD.Prelude
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility

/-!
# maximum_matching_unmatched_independent

Topic: graphs   Node: 2b138b75a62e

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

The vertices left uncovered by a maximum matching inside a vertex set form an independent set.
-/

theorem maximum_matching_unmatched_independent
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (M : G.Subgraph) (hM : M.IsMatching)
    (hMS : M.verts ⊆ (S : Set V))
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.verts ⊆ (S : Set V) → N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    ∀ u ∈ S, u ∉ M.verts → ∀ v ∈ S, v ∉ M.verts → ¬ G.Adj u v := by
  set_option maxHeartbeats 4000000 in
    classical
    intro u hu huM v hv hvM huv
    let f : Fin 1 → V := fun _ => u
    let g : Fin 1 → V := fun _ => v
    have hf : Function.Injective f := by intro a b h; exact Subsingleton.elim a b
    have hg : Function.Injective g := by intro a b h; exact Subsingleton.elim a b
    have hfg : ∀ a b, f a ≠ g b := by intro a b; exact G.ne_of_adj huv
    obtain ⟨E,hE,hEcard,hEverts⟩ := indexed_disjoint_cross_edges_form_matching G 1 f g hf hg hfg (by intro a; exact huv)
    have hdis : Disjoint M.verts E.verts := by
      apply Set.disjoint_left.mpr
      intro x hxM hxE
      rw [hEverts] at hxE
      rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
      · exact huM (by simpa [f,hi] using hxM)
      · exact hvM (by simpa [g,hi] using hxM)
    have hsup := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard M E hM hE hdis
    have hsub : (M ⊔ E).verts ⊆ (S : Set V) := by
      intro x hx
      change x ∈ M.verts ∪ E.verts at hx
      rcases hx with hxM | hxE
      · exact hMS hxM
      · rw [hEverts] at hxE
        rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
        · simpa [f,hi] using hu
        · simpa [g,hi] using hv
    have hbound := hmax (M ⊔ E) hsup.1 hsub
    rw [hsup.2,hEcard] at hbound
    omega
