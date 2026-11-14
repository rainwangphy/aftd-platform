import AFTD.Prelude

/-!
# graph_125_noncolorable_complement_high_degree

Topic: graphs   Node: fd1c997d1b0c

Provenance: helper lemma. Minimum-degree coloring reduction for OP-110.

If a 125-vertex graph has independence number at most three and its complement is not three-colorable, then it has a vertex of degree at least 46.
-/

theorem graph_125_noncolorable_complement_high_degree
    (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj]
    (hindep : G.IndepSetFree 4) (hcolor : ¬ Gᶜ.Colorable 3) :
    ∃ x, 46 ≤ G.degree x := by
  classical
  by_contra hn
  have hd : ∀ v, G.degree v ≤ 45 := by
    intro v
    by_contra hv
    exact hn ⟨v, by omega⟩
  have hf : Gᶜ.CliqueFree 4 := by simpa using hindep
  have hmin : 79 ≤ Gᶜ.minDegree := by
    apply Gᶜ.le_minDegree_of_forall_le_degree
    intro v
    rw [G.degree_compl]
    simp only [Fintype.card_fin]
    have hv := hd v
    omega
  have hth : (3*3-4)*Fintype.card (Fin 125)/(3*3-1) < Gᶜ.minDegree := by
    norm_num
    omega
  exact hcolor (SimpleGraph.colorable_of_cliqueFree_lt_minDegree (G := Gᶜ) (r := 3) hf hth)
