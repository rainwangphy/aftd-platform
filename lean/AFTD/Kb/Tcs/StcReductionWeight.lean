import AFTD.Prelude

/-!
# stc_reduction_weight

Topic: approximation   Node: 8262cab9e068

Provenance: helper lemma. step towards weighted_spanning_tree_congestion_hardness_gap

The edge weight `w` on `H_A`: `1` on every edge of `Q` and on every edge `{s_i, w_{ij}}`, `A + 1` on every edge `{w_{ij}, t_i}`, and `0` elsewhere.
-/

/-- The weight function of the reduction: weight `1` on the edges of `Q` (and on the light gadget edges `s_i w_{ij}`), weight `A + 1` on the heavy gadget edges `w_{ij} t_i`, and `0` on non-edges. -/
noncomputable def stc_reduction_weight {V : Type*} [DecidableEq V] {p : ℕ} (s t : Fin p → V) (A : ℕ) :
    Sym2 (Sum V (Fin p × Fin A)) → ℕ := Sym2.lift ⟨fun x y =>
    match x, y with
    | Sum.inl _, Sum.inl _ => 1
    | Sum.inl u, Sum.inr (i, _) => if u = t i then A + 1 else 1
    | Sum.inr (i, _), Sum.inl u => if u = t i then A + 1 else 1
    | Sum.inr _, Sum.inr _ => 0,
   fun x y => by cases x <;> cases y <;> rfl⟩
