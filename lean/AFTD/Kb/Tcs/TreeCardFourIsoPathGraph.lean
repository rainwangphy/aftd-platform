import AFTD.Prelude
import AFTD.Kb.Tcs.TreeCardFourPathEdges

/-!
# tree_card_four_iso_path_graph

Topic: graphs   Node: 2029ffd50ef9

Provenance: helper lemma. step towards tree_card_four_iso_of_degree_le_two

Any tree on 4 vertices with all degrees at most 2 is isomorphic to the standard path graph pathGraph 4.
-/

/-- Any tree on 4 vertices with all degrees at most 2 is isomorphic to the standard path graph on 4 vertices. -/
theorem tree_card_four_iso_path_graph {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : Fintype.card V = 4)
    (hdeg : ∀ v : V, T.degree v ≤ 2) :
    Nonempty (T ≃g SimpleGraph.pathGraph 4) := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, -, h_adj⟩ :=
    tree_card_four_path_edges T hT hcard hdeg
  let f : Fin 4 → V := ![a, b, c, d]
  have hinj : Function.Injective f := by
    intro u v h
    fin_cases u <;> fin_cases v <;> aesop
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [Fintype.card_fin, hcard]⟩
  let e : Fin 4 ≃ V := Equiv.ofBijective f hbij
  have h_rel : ∀ {u v : Fin 4}, T.Adj (e u) (e v) ↔ (SimpleGraph.pathGraph 4).Adj u v := by
    intro u v
    fin_cases u <;> fin_cases v <;>
      { rw [SimpleGraph.pathGraph_adj, h_adj]
        dsimp [e, f, Equiv.ofBijective]
        aesop }
  have r : (SimpleGraph.pathGraph 4).Adj ≃r T.Adj := RelIso.mk e h_rel
  exact ⟨r.symm⟩
