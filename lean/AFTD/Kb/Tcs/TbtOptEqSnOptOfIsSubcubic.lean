import AFTD.Prelude
import AFTD.Kb.Tcs.TbtOpt
import AFTD.Kb.Tcs.TbtSnOpt
import AFTD.Kb.Tcs.IsSubcubicTree
import AFTD.Kb.Tcs.TreeRoutingCost

/-!
# tbt_opt_eq_sn_opt_of_is_subcubic

Topic: approximation   Node: 15d7b23859f4

Provenance: helper lemma. arXiv:2610.39863, Section 3

For every finite type V with at least two elements and every subcubic tree T on V, tbt_opt T equals tbt_sn_opt T.
-/

open Classical in
lemma tbt_opt_eq_sn_opt_of_is_subcubic_cost_ge_card {V W : Type*} [Fintype V] (T : SimpleGraph V) (H : SimpleGraph W)
    (hH : H.Connected) (f : V ↪ W) :
    T.edgeFinset.card ≤ tree_routing_cost T H f := by
  rw [tree_routing_cost]
  have h_le : ∀ e ∈ T.edgeFinset, 1 ≤ Sym2.lift ⟨fun u v ↦ H.dist (f u) (f v), fun _ _ ↦ H.dist_comm⟩ e := by
    intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hne : u ≠ v := T.ne_of_adj he
    have hne' : f u ≠ f v := f.injective.ne hne
    exact hH.pos_dist_of_ne hne'
  have hcard : T.edgeFinset.card = ∑ e ∈ T.edgeFinset, 1 := Finset.card_eq_sum_ones T.edgeFinset
  rw [hcard]
  exact Finset.sum_le_sum h_le

open Classical in
lemma tbt_opt_eq_sn_opt_of_is_subcubic_cost_self_id {V : Type*} [Fintype V] (T : SimpleGraph V) :
    tree_routing_cost T T id = T.edgeFinset.card := by
  rw [tree_routing_cost]
  have h_eq : ∀ e ∈ T.edgeFinset, Sym2.lift ⟨fun u v ↦ T.dist (id u) (id v), fun _ _ ↦ T.dist_comm⟩ e = 1 := by
    intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk, id]
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact SimpleGraph.dist_eq_one_iff_adj.mpr he
  have hsum : (∑ e ∈ T.edgeFinset, Sym2.lift ⟨fun u v ↦ T.dist (id u) (id v), fun _ _ ↦ T.dist_comm⟩ e) =
      ∑ e ∈ T.edgeFinset, 1 := Finset.sum_congr rfl h_eq
  rw [hsum, ← Finset.card_eq_sum_ones]

/-- For any demand tree that is already subcubic, the terminal-only and Steiner binary host routing optima are equal. -/
theorem tbt_opt_eq_sn_opt_of_is_subcubic {V : Type} [Fintype V]
    (T : SimpleGraph V) (hT : is_subcubic_tree T) (hn : 2 ≤ Fintype.card V) :
    tbt_opt T = tbt_sn_opt T := by
  classical
  have _ := hn
  have h_opt : tbt_opt T = T.edgeFinset.card := by
    rw [tbt_opt]
    apply le_antisymm
    · apply Nat.sInf_le
      exact ⟨T, hT, tbt_opt_eq_sn_opt_of_is_subcubic_cost_self_id T⟩
    · apply le_csInf
      · exact ⟨T.edgeFinset.card, ⟨T, hT, tbt_opt_eq_sn_opt_of_is_subcubic_cost_self_id T⟩⟩
      · rintro c ⟨H, hH, rfl⟩
        have hconn : H.Connected := hH.1.connected
        exact tbt_opt_eq_sn_opt_of_is_subcubic_cost_ge_card T H hconn (Function.Embedding.refl V)
  have h_sn : tbt_sn_opt T = T.edgeFinset.card := by
    rw [tbt_sn_opt]
    apply le_antisymm
    · apply Nat.sInf_le
      exact ⟨V, inferInstance, T, hT, Function.Embedding.refl V, tbt_opt_eq_sn_opt_of_is_subcubic_cost_self_id T⟩
    · apply le_csInf
      · exact ⟨T.edgeFinset.card, ⟨V, inferInstance, T, hT, Function.Embedding.refl V, tbt_opt_eq_sn_opt_of_is_subcubic_cost_self_id T⟩⟩
      · rintro c ⟨W, _, H, hH, f, rfl⟩
        have hconn : H.Connected := hH.1.connected
        exact tbt_opt_eq_sn_opt_of_is_subcubic_cost_ge_card T H hconn f
  rw [h_opt, h_sn]
