import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeBlocksFourAndSixSwitches

/-!
# forced_matching_edge_excludes_adjacent_true_twin

Topic: graphs   Node: f38269f3ddae

Provenance: helper lemma. OP-1957; residual exclusion for the saturated three-vertex boundary block.

A forced edge of a perfect matching cannot have an endpoint with a distinct adjacent true twin other than the edge's other endpoint.
-/

theorem forced_matching_edge_excludes_adjacent_true_twin
    {V : Type*} (H : SimpleGraph V) (P : H.Subgraph) (hP : P.IsPerfectMatching)
    (x y a : V) (hxy : P.Adj x y) (hax : a ≠ x) (hay : a ≠ y)
    (hxa : H.Adj x a)
    (htwin : ∀ z, z ≠ x → z ≠ a → (H.Adj x z ↔ H.Adj a z))
    (hforced : ∀ Q : H.Subgraph, Q.IsPerfectMatching → Q.Adj x y) : False := by
  classical
  obtain ⟨w, haw, -⟩ := hP.1 (hP.2 a)
  have hxy_ne : x ≠ y := hxy.ne
  have hxa_ne : x ≠ a := hax.symm
  have hya_ne : y ≠ a := hay.symm
  have haw_ne : a ≠ w := haw.ne
  have hxw_ne : x ≠ w := by
    intro h
    have h1 : P.Adj x a := h ▸ haw.symm
    have h_eq : a = y := hP.1.eq_of_adj_left h1 hxy
    exact hay h_eq
  have hyw_ne : y ≠ w := by
    intro h
    have h1 : P.Adj y a := h ▸ haw.symm
    have h_eq : a = x := hP.1.eq_of_adj_left h1 hxy.symm
    exact hax h_eq
  have hinj : Function.Injective (![x, y, a, w] : Fin 4 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals {
      dsimp at hij
      subst hij
      first | exact (hxy_ne rfl).elim | exact (hxa_ne rfl).elim | exact (hxw_ne rfl).elim
            | exact (hya_ne rfl).elim | exact (hyw_ne rfl).elim | exact (haw_ne rfl).elim
    }
  have hya : H.Adj y a := by
    have hyx : y ≠ x := hxy.ne.symm
    have h_xy_sub : H.Adj x y := P.adj_sub hxy
    exact ((htwin y hyx hya_ne).mp h_xy_sub).symm
  have hxw : H.Adj x w := by
    have hwx : w ≠ x := hxw_ne.symm
    have hwa : w ≠ a := haw_ne.symm
    have h_aw : H.Adj a w := P.adj_sub haw
    exact (htwin w hwx hwa).mpr h_aw
  have hblock := (forced_matching_edge_blocks_four_and_six_switches H P hP x y hxy hforced).1
  exact hblock ⟨a, w, hinj, haw, hya, hxw⟩
