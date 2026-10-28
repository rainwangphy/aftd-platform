import AFTD.Prelude

/-!
# is_tree_card_coloring_three_subsingleton

Topic: graphs   Node: 33e698c3961d

Provenance: helper lemma. step towards is_tree_card_coloring_three

A graph on a singleton vertex type has exactly 3 proper 3-colorings.
-/

/-- A graph on a singleton vertex type has exactly 3 proper 3-colorings. -/
lemma is_tree_card_coloring_three_subsingleton {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] [Subsingleton V] [Nonempty V] :
    Fintype.card (T.Coloring (Fin 3)) = 3 := by
  have e : T.Coloring (Fin 3) ≃ (V → Fin 3) := {
    toFun := fun C => C
    invFun := fun f => SimpleGraph.Coloring.mk f (fun {v w} h => by
      have : v = w := Subsingleton.elim v w
      subst this
      exact (T.irrefl h).elim)
    left_inv := fun C => by ext; rfl
    right_inv := fun f => rfl
  }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [Fintype.card_eq_one_of_forall_eq (fun j => Subsingleton.elim j v)]
  rfl
