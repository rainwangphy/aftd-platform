import AFTD.Prelude

/-!
# stc_reduction_gadget

Topic: approximation   Node: f9c101454405

Provenance: helper lemma. step towards weighted_spanning_tree_congestion_hardness_gap

The graph `H_A` obtained from `Q` by adding, for every pair `i` and every `j < A`, a new vertex `w_{ij}` joined to `s_i` and to `t_i`.
-/

/-- The reduction graph `H_A` on `V ⊕ (Fin p × Fin A)`: the edges of `Q` on the `V` part, plus, for each `(i,j)`, the two edges joining the auxiliary vertex `(i,j)` to `s i` and to `t i`. -/
def stc_reduction_gadget {V : Type*} (Q : SimpleGraph V) {p : ℕ} (s t : Fin p → V) (A : ℕ) :
    SimpleGraph (Sum V (Fin p × Fin A)) :=
  let H_adj : Sum V (Fin p × Fin A) → Sum V (Fin p × Fin A) → Prop := fun x y =>
    match x, y with
    | Sum.inl u, Sum.inl v => Q.Adj u v
    | Sum.inl u, Sum.inr (i, _) => u = s i ∨ u = t i
    | Sum.inr (i, _), Sum.inl u => u = s i ∨ u = t i
    | Sum.inr _, Sum.inr _ => False
  ⟨H_adj,
   ⟨fun x y => by
      rcases x with u | ⟨i, j⟩ <;> rcases y with v | ⟨i', j'⟩
      · exact fun h => h.symm
      · exact id
      · exact id
      · exact fun h => h.elim⟩,
   ⟨fun x => by
      rcases x with u | ⟨i, j⟩
      · exact Q.irrefl
      · exact fun h => h⟩⟩
