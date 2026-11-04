import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleFreeUniqueNeighborhoodNeighborsCardLe

/-!
# simple_graph_ramsey_three_ten_nine_regular_outer_degree_eight_card_le

Topic: combinatorics   Node: 6ac96c8632b8

Provenance: helper lemma. Regular neighborhood-gluing obstruction for OP-926.

For a 9-regular triangle-free graph on 40 vertices with no independent ten-set, the induced graph outside the closed neighborhood of any vertex has at most nine vertices of degree 8.
-/

/-- An outer degree-8 vertex has exactly one neighbour in the neighbourhood of `v`. -/
private theorem simple_graph_ramsey_three_ten_nine_regular_outer_degree_eight_card_le_aux
    (g : SimpleGraph (Fin 40)) [DecidableRel g.Adj]
    (hreg : ∀ z, g.degree z = 9) (v : Fin 40)
    (x : Fin 40) (hx : x ≠ v ∧ ¬ g.Adj v x)
    (hdeg : (g.induce {u : Fin 40 | u ≠ v ∧ ¬ g.Adj v u}).degree
        (⟨x, hx⟩ : {u : Fin 40 // u ≠ v ∧ ¬ g.Adj v u}) = 8) :
    ∃! w, g.Adj v w ∧ g.Adj w x := by
  classical
  let S : Set (Fin 40) := {u : Fin 40 | u ≠ v ∧ ¬ g.Adj v u}
  let N : Finset (Fin 40) := g.neighborFinset x
  have hN : N.card = 9 := by
    simpa [N] using (SimpleGraph.card_neighborFinset_eq_degree (G := g) (v := x)).trans (hreg x)
  have hmap := SimpleGraph.map_neighborFinset_induce (G := g) (s := S) (v := (⟨x, hx⟩ : S))
  have hS : (N ∩ S.toFinset).card = 8 := by
    have h : ((g.neighborFinset x) ∩ S.toFinset).card = 8 := by
      rw [← hmap, Finset.card_map]
      exact hdeg
    simpa [N] using h
  have hIn : (N.filter (fun w => w ∈ S)).card = 8 := by
    rw [← Finset.filter_mem_eq_inter] at hS
    simpa using hS
  have hcomp : (N.filter (fun w => ¬ w ∈ S)).card = 1 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := N) (p := fun w => w ∈ S)
    omega
  let T : Finset (Fin 40) := N.filter (fun w => g.Adj v w)
  have hTeq : (N.filter (fun w => ¬ w ∈ S)) = T := by
    ext w
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hwN, hwS⟩
      have hAdjxw : g.Adj x w := (SimpleGraph.mem_neighborFinset g x w).mp hwN
      have hAdjvw : g.Adj v w := by
        by_contra h
        apply hwS
        change w ≠ v ∧ ¬ g.Adj v w
        refine ⟨?_, h⟩
        intro hwv
        subst hwv
        exact hx.2 hAdjxw.symm
      exact ⟨hwN, hAdjvw⟩
    · rintro ⟨hwN, hAdjvw⟩
      refine ⟨hwN, ?_⟩
      intro hwS
      have hwS' : w ≠ v ∧ ¬ g.Adj v w := by
        simpa [S] using hwS
      exact hwS'.2 hAdjvw
  have hTcard : T.card = 1 := by
    rw [← hTeq]
    exact hcomp
  obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hTcard
  refine ⟨w0, ?_, ?_⟩
  · have hw0T : w0 ∈ T := by
      rw [hw0]
      simp
    change w0 ∈ N.filter (fun w => g.Adj v w) at hw0T
    rw [Finset.mem_filter] at hw0T
    exact ⟨hw0T.2, ((SimpleGraph.mem_neighborFinset g x w0).mp hw0T.1).symm⟩
  · intro y hy
    have hyT : y ∈ T := by
      change y ∈ N.filter (fun w => g.Adj v w)
      rw [Finset.mem_filter]
      exact ⟨(SimpleGraph.mem_neighborFinset g x y).mpr hy.2.symm, hy.1⟩
    have hys : y ∈ ({w0} : Finset (Fin 40)) := by
      rw [← hw0]
      exact hyT
    simpa using hys

theorem simple_graph_ramsey_three_ten_nine_regular_outer_degree_eight_card_le
    (g : SimpleGraph (Fin 40)) [DecidableRel g.Adj]
    (htri : g.CliqueFree 3) (hfree : gᶜ.CliqueFree 10)
    (hreg : ∀ v, g.degree v = 9) (v : Fin 40) :
    ((Finset.univ : Finset {u : Fin 40 // u ≠ v ∧ ¬ g.Adj v u}).filter
      (fun x => (g.induce {u | u ≠ v ∧ ¬ g.Adj v u}).degree x = 8)).card ≤ 9 := by
  classical
  let F : Finset {u : Fin 40 // u ≠ v ∧ ¬ g.Adj v u} :=
    Finset.univ.filter (fun x => (g.induce {u | u ≠ v ∧ ¬ g.Adj v u}).degree x = 8)
  change F.card ≤ 9
  let Q : Finset (Fin 40) := F.image Subtype.val
  have hQcard : Q.card = F.card := by
    change (F.image Subtype.val).card = F.card
    exact Finset.card_image_of_injective F Subtype.val_injective
  rw [← hQcard]
  have hbound := simple_graph_triangle_free_unique_neighborhood_neighbors_card_le
      (G := g) (k := 10) htri hfree v (by rw [hreg v]) Q ?_
  · simpa [hreg v] using hbound
  · intro x hxQ
    change x ∈ F.image Subtype.val at hxQ
    rcases Finset.mem_image.mp hxQ with ⟨y, hyF, hyx⟩
    have hydeg : (g.induce {u | u ≠ v ∧ ¬ g.Adj v u}).degree y = 8 :=
      (Finset.mem_filter.mp hyF).2
    subst x
    exact simple_graph_ramsey_three_ten_nine_regular_outer_degree_eight_card_le_aux
      g hreg v y.val y.2 hydeg
