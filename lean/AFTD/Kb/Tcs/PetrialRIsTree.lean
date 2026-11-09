import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialRGraph
import AFTD.Kb.Physics.InstDecidableRelPathGraph
import AFTD.Kb.Tcs.InstDecidableRelPetrialRGraphAdj
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.G

/-!
# petrial_R_is_tree

Topic: combinatorics   Node: 6c1f4fa8ab0a

Provenance: helper lemma. arXiv:2611.07503 Section 3

For every natural number m, the graph R_m is a tree.
-/

def petrial_R_is_tree_fiber_hom (m : ℕ) (i : Fin m) :
    SimpleGraph.pathGraph 5 →g petrial_R_graph m where
  toFun v := some (i, v)
  map_rel' h := ⟨rfl, h⟩

theorem petrial_R_is_tree_connected (m : ℕ) : (petrial_R_graph m).Connected := by
  have : Nonempty (Option (Fin m × Fin 5)) := ⟨none⟩
  refine SimpleGraph.Connected.mk fun u v => ?_
  have h_to_none (x : Option (Fin m × Fin 5)) : (petrial_R_graph m).Reachable x none := by
    match x with
    | none => exact SimpleGraph.Reachable.refl none
    | some (i, v) =>
      have hr : (SimpleGraph.pathGraph 5).Reachable v 2 :=
        (SimpleGraph.pathGraph_connected 4).preconnected v 2
      have hr' : (petrial_R_graph m).Reachable (some (i, v)) (some (i, 2)) :=
        hr.map (petrial_R_is_tree_fiber_hom m i)
      have hadj : (petrial_R_graph m).Adj (some (i, 2)) none := rfl
      exact hr'.trans hadj.reachable
  exact (h_to_none u).trans (h_to_none v).symm

def petrial_R_is_tree_dart_equiv (m : ℕ) :
    (petrial_R_graph m).Dart ≃ Fin m ⊕ (Fin m ⊕ (Fin m × (SimpleGraph.pathGraph 5).Dart)) where
  toFun d :=
    match d with
    | ⟨(none, none), h⟩ => False.elim h
    | ⟨(none, some (i, v)), h⟩ =>
      Sum.inl i
    | ⟨(some (i, v), none), h⟩ =>
      Sum.inr (Sum.inl i)
    | ⟨(some (i₁, v₁), some (i₂, v₂)), h⟩ =>
      Sum.inr (Sum.inr (i₁, ⟨(v₁, v₂), h.2⟩))
  invFun x :=
    match x with
    | Sum.inl i => ⟨(none, some (i, 2)), rfl⟩
    | Sum.inr (Sum.inl i) => ⟨(some (i, 2), none), rfl⟩
    | Sum.inr (Sum.inr (i, d)) => ⟨(some (i, d.fst), some (i, d.snd)), ⟨rfl, d.adj⟩⟩
  left_inv d := by
    rcases d with ⟨⟨a, b⟩, h⟩
    rcases a with _ | ⟨i₁, v₁⟩ <;> rcases b with _ | ⟨i₂, v₂⟩
    · exact False.elim h
    · dsimp; cases h; rfl
    · dsimp; cases h; rfl
    · dsimp; obtain ⟨rfl, hadj⟩ := h; rfl
  right_inv x := by
    rcases x with i | (i | ⟨i, ⟨⟨v₁, v₂⟩, hadj⟩⟩) <;> rfl

/-- For every m, R_m is a tree. -/
theorem petrial_R_is_tree (m : ℕ) : (petrial_R_graph m).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨petrial_R_is_tree_connected m, ?_⟩
  have h_path : Fintype.card (SimpleGraph.pathGraph 5).Dart = 8 := by decide
  have h_dart : Fintype.card (petrial_R_graph m).Dart = 10 * m := by
    rw [Fintype.card_congr (petrial_R_is_tree_dart_equiv m)]
    simp [h_path]
    omega
  have hd := SimpleGraph.dart_card_eq_twice_card_edges (petrial_R_graph m)
  rw [h_dart] at hd
  have he : Nat.card ↑(petrial_R_graph m).edgeSet = (petrial_R_graph m).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  have hv : Nat.card (Option (Fin m × Fin 5)) = 5 * m + 1 := by
    simp; omega
  omega
