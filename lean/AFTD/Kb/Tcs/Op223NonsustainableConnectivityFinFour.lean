import AFTD.Prelude
import AFTD.Kb.Tcs.Op223NonsustainableTreeFinFour
import AFTD.Kb.Tcs.NonsustainableGtsStep
import AFTD.Kb.Tcs.IsNonsustainableTree

/-!
# op223_nonsustainable_connectivity_fin_four

Topic: graphs   Node: 20df2ea1f7bf

Provenance: helper lemma. arXiv:2610.17078, Open Problem 6.1

Every non-sustainable tree X on Fin 4 can reach a star graph isomorphic to completeBipartiteGraph (Fin 1) (Fin 3) by a sequence of non-sustainable generalized tree shifts.
-/

/-- Every non-sustainable tree on four vertices can reach a star K_{1,3} by non-sustainable generalized tree shifts. -/
theorem op223_nonsustainable_connectivity_fin_four (X : SimpleGraph (Fin 4))
    (hX : is_nonsustainable_tree X) :
    ∃ K : SimpleGraph (Fin 4), Nonempty (K ≃g completeBipartiteGraph (Fin 1) (Fin 3)) ∧
      Relation.ReflTransGen nonsustainable_gts_step X K := ⟨X, op223_nonsustainable_tree_fin_four X hX, Relation.ReflTransGen.refl⟩
