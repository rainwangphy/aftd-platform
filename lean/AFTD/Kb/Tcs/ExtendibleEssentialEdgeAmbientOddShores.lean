import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierPartitionAllCases
import AFTD.Kb.Tcs.GraphIsoOddComponentsCard

/-!
# extendible_essential_edge_ambient_odd_shores

Topic: graphs   Node: 131bd08b0e1d

Provenance: helper lemma. OP-1957: ambient transfer from the forced residual matching barrier to the positive- and zero-barrier assembly.

For an essential edge xy of a k-extendible graph on 4k vertices, there are disjoint ambient vertex sets X, Y and U and a natural number s: X and Y are odd and contain x and y, their total size with U and s is 2k, U has at least s odd components and has the same parity as s, U is anticomplete to X and Y, and xy is the only possible X-to-Y edge.
-/

theorem extendible_essential_edge_ambient_odd_shores
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (x y : Fin (4*k)) (hxy : G.Adj x y) (hext : is_k_extendable G k)
    (hess : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k) :
    ∃ (X Y U : Finset (Fin (4*k))) (s : ℕ),
      Disjoint X Y ∧ Disjoint X U ∧ Disjoint Y U ∧
      x ∈ X ∧ y ∈ Y ∧ Odd X.card ∧ Odd Y.card ∧
      X.card + Y.card + U.card + s = 2*k ∧
      s ≤ (G.induce {v | v ∈ U}).oddComponents.ncard ∧ U.card % 2 = s % 2 ∧
      (∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y) ∧
      (∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u) ∧
      (∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u) := by
  classical
  obtain ⟨R,hR,hx,hy,hP,hforced⟩ := k_extendable_essential_edge_has_forced_matching_residual (4*k) k G x y hxy hext hess
  let H := G.induce {v | v ∈ R}
  let x' : {v : Fin (4*k) | v ∈ R} := ⟨x,hx⟩
  let y' : {v : Fin (4*k) | v ∈ R} := ⟨y,hy⟩
  obtain ⟨S,X,Y,U,hSX,hSY,hSU,hXY,hXU,hYU,hcover,hxX,hyY,hcross,hanti,hodd,hoddX,hoddY⟩ :=
    forced_matching_edge_barrier_partition_all_cases H x' y' hxy hP hforced
  let f : {v : Fin (4*k) | v ∈ R} ↪ Fin (4*k) := ⟨Subtype.val, Subtype.val_injective⟩
  have hmem : ∀ (T : Finset {v : Fin (4*k) | v ∈ R}) (z : {v : Fin (4*k) | v ∈ R}), z.val ∈ T.map f ↔ z ∈ T := by
    intro T z
    simp [f]
  have hd : ∀ (T W : Finset {v : Fin (4*k) | v ∈ R}), Disjoint T W → Disjoint (T.map f) (W.map f) := by
    intro T W h
    apply Finset.disjoint_left.mpr
    intro z hzT hzW
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hzT
    obtain ⟨b, hb, he2⟩ := Finset.mem_map.mp hzW
    have hab : a = b := f.injective (he.trans he2.symm)
    exact (Finset.disjoint_left.mp h) ha (hab ▸ hb)
  have hcard : S.card + X.card + Y.card + U.card = R.card := by
    have ha : Disjoint (S ∪ X) Y := Finset.disjoint_union_left.mpr ⟨hSY,hXY⟩
    have hb : Disjoint (S ∪ X ∪ Y) U := Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hSU,hXU⟩,hYU⟩
    have hc := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hb, Finset.card_union_of_disjoint ha, Finset.card_union_of_disjoint hSX] at hc
    simpa using hc
  have hpar : U.card % 2 = S.card % 2 := by
    obtain ⟨a,ha⟩ := hoddX
    obtain ⟨b,hb⟩ := hoddY
    omega
  let e : (H.induce {v | v ∈ U}) ≃g (G.induce {v | v ∈ U.map f}) := {
    toFun := fun z => ⟨z.val.val,(hmem U z.val).2 z.property⟩
    invFun := fun z => ⟨⟨z.val, by
      obtain ⟨w,hw,he⟩ := Finset.mem_map.mp z.property
      exact he ▸ w.property⟩, by
        apply (hmem U _).1
        exact z.property⟩
    left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro z; apply Subtype.ext; rfl
    map_rel_iff' := by intro a b; rfl }
  have hiso := graph_iso_odd_components_card _ _ e
  refine ⟨X.map f,Y.map f,U.map f,S.card,hd X Y hXY,hd X U hXU,hd Y U hYU,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hmem X x').2 hxX
  · exact (hmem Y y').2 hyY
  · simpa using hoddX
  · simpa using hoddY
  · simp only [Finset.card_map]; omega
  · rw [← hiso]; exact hodd
  · simpa using hpar
  · intro a ha b hb hab
    obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨ha,hb⟩ := hcross a' ha' b' hb' hab
    exact ⟨congrArg Subtype.val ha,congrArg Subtype.val hb⟩
  · intro a ha u hu hau
    obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨u',hu',rfl⟩ := Finset.mem_map.mp hu
    exact hanti u' hu' a' (Finset.mem_union_left Y ha') hau.symm
  · intro b hb u hu hbu
    obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨u',hu',rfl⟩ := Finset.mem_map.mp hu
    exact hanti u' hu' b' (Finset.mem_union_right X hb') hbu.symm
