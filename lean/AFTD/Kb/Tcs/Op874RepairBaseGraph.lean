import AFTD.Prelude
import AFTD.Kb.Tcs.Op874RepairBaseRight
import AFTD.Kb.Tcs.Op874RepairBaseLeft

/-!
# op874_repair_base_graph

Topic: graphs   Node: e846ba1c72af

Provenance: helper lemma. step towards op874_repair_chain_data

The twenty-vertex repair block as a simple graph on its own, with its 29 internal edges; the adjacency is stated as an existential over the edge index so that it is computably decidable.
-/

/-- The twenty-vertex repair block as a simple graph, with a computably decidable adjacency. -/
abbrev op874_repair_base_graph : SimpleGraph (Fin 20) where
  Adj u v := ∃ j : Fin 29,
    s(op874_repair_base_left j.castSucc, op874_repair_base_right j.castSucc) = s(u, v)
  symm := ⟨fun u v h => h.imp fun j hj => hj.trans Sym2.eq_swap⟩
  loopless := ⟨fun u h => by
    obtain ⟨j, hj⟩ := h
    have key : ∀ j : Fin 29,
        ¬ (s(op874_repair_base_left j.castSucc, op874_repair_base_right j.castSucc)).IsDiag := by
      intro j; revert j; decide
    exact key j (hj.symm ▸ Sym2.mk_isDiag_iff.mpr rfl)⟩
