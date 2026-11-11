import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsNutGraph

/-!
# simple_graph_diam_two_nut_graph_card_ge_four

Topic: graphs   Node: 6b1da59d2b76

Provenance: helper lemma. step towards op_1267_diameter_two_nut_graph_has_binary_vector

Every finite simple nut graph of diameter 2 has at least 4 vertices.
-/

/-- Every finite simple nut graph of diameter 2 has at least 4 vertices. -/
theorem simple_graph_diam_two_nut_graph_card_ge_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnut : simple_graph_is_nut_graph G) (hdiam : G.diam = 2) :
    4 ≤ Fintype.card V := by
  have hne : G.diam ≠ 0 := by omega
  have hnt : Nontrivial V := SimpleGraph.nontrivial_of_diam_ne_zero hne
  obtain ⟨u, v, huv⟩ := SimpleGraph.exists_dist_eq_diam (G := G)
  rw [hdiam] at huv
  have hreach : G.Reachable u v := SimpleGraph.Reachable.of_dist_ne_zero (by omega)
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have hplen : p.length = 2 := by rw [hp, huv]
  set w : V := p.getVert 1 with hwdef
  have huw : G.Adj u w := by
    have h := SimpleGraph.Walk.adj_getVert_succ p (i := 0) (by omega)
    simpa [w, SimpleGraph.Walk.getVert_zero] using h
  have hwv : G.Adj w v := by
    have h := SimpleGraph.Walk.adj_getVert_succ p (i := 1) (by omega)
    have h2 : p.getVert 2 = v := by
      have := SimpleGraph.Walk.getVert_length p
      rwa [hplen] at this
    simpa [w, h2] using h
  have hwv' : G.Adj v w := (SimpleGraph.adj_comm G w v).mp hwv
  have hnotadj : ¬ G.Adj u v := by
    rw [← SimpleGraph.dist_eq_one_iff_adj]
    omega
  have hnotadj' : ¬ G.Adj v u := fun h => hnotadj ((SimpleGraph.adj_comm G v u).mp h)
  have huw_ne : u ≠ w := huw.ne
  have hwv_ne : w ≠ v := hwv.ne
  have huv_ne : u ≠ v := by
    rintro rfl
    rw [SimpleGraph.dist_self] at huv
    omega
  have hcard3 : ({u, w, v} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact hwv_ne
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim huw_ne huv_ne
  have hge3 : 3 ≤ Fintype.card V := by
    have h := Finset.card_le_card (Finset.subset_univ ({u, w, v} : Finset V))
    rw [Finset.card_univ] at h
    omega
  by_contra hcon
  simp only [not_le] at hcon
  have hcard : Fintype.card V = 3 := by omega
  have huniv : ({u, w, v} : Finset V) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard3, hcard])
  have hmem3 : ∀ x : V, x = u ∨ x = w ∨ x = v := by
    intro x
    have hx : x ∈ ({u, w, v} : Finset V) := by rw [huniv]; exact Finset.mem_univ x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  have hAdj : ∀ x : V, G.Adj u x ↔ G.Adj v x := by
    intro x
    rcases hmem3 x with rfl | rfl | rfl
    · exact ⟨fun h => absurd h (SimpleGraph.irrefl G), fun h => absurd h hnotadj'⟩
    · exact ⟨fun _ => hwv', fun _ => huw⟩
    · exact ⟨fun h => absurd h hnotadj, fun h => absurd h (SimpleGraph.irrefl G)⟩
  have hrow : ∀ x : V, (SimpleGraph.adjMatrix ℝ G) u x = (SimpleGraph.adjMatrix ℝ G) v x := by
    intro x
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj u x
    · rw [if_pos h, if_pos ((hAdj x).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hAdj x).mpr hh))]
  have hsymm : ∀ a b : V, (SimpleGraph.adjMatrix ℝ G) a b = (SimpleGraph.adjMatrix ℝ G) b a := by
    intro a b
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj a b
    · rw [if_pos h, if_pos ((SimpleGraph.adj_comm G a b).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((SimpleGraph.adj_comm G a b).mpr hh))]
  set y : V → ℝ := Pi.single u (1:ℝ) - Pi.single v (1:ℝ) with hydef
  have hmem : y ∈ (Matrix.toLin' (SimpleGraph.adjMatrix ℝ G)).ker := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hydef, Matrix.mulVec_sub,
      Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    funext x
    simp only [Pi.sub_apply, Matrix.col_apply, Pi.zero_apply]
    rw [hsymm x u, hsymm x v]
    exact sub_eq_zero.mpr (hrow x)
  have hyne : y ≠ 0 := by
    intro h
    have h1 : y u = (0 : V → ℝ) u := by rw [h]
    simp [hydef, Pi.single_eq_same, Pi.single_eq_of_ne huv_ne] at h1
  have hzero : y w = 0 := by
    simp [hydef, Pi.single_eq_of_ne (Ne.symm huw_ne), Pi.single_eq_of_ne hwv_ne]
  exact (hnut.2 y hmem hyne w) hzero
