import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated

/-!
# uniquely_k4_saturated_max_degree_ge_three

Topic: graphs   Node: 80ad389ade34

Provenance: helper lemma. arXiv:2611.13656 Sec. 1

For every finite simple graph G on at least 4 vertices, if G is uniquely K_4-saturated, then the maximum degree of G is at least 3.
-/

open scoped Classical in
/-- Every uniquely K_4-saturated simple graph on at least 4 vertices has maximum degree at least 3. -/
theorem uniquely_k4_saturated_max_degree_ge_three
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : 4 ≤ Fintype.card V)
    (hG : is_uniquely_clique_saturated G 4) :
    3 ≤ G.maxDegree := by
  classical
  obtain ⟨s0, -, hs0card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (by simpa using hn)
  have hex : ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v := by
    by_contra h
    have hclique : G.IsClique ↑s0 := by
      intro a ha b hb hab
      by_contra hnab
      exact h ⟨a, b, hab, hnab⟩
    exact hG.1 s0 ⟨hclique, hs0card⟩
  obtain ⟨u, v, huv, hnv⟩ := hex
  have he : s(u, v) ∈ Gᶜ.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.compl_adj G u v).mpr ⟨huv, hnv⟩
  obtain ⟨t, ht, -⟩ := hG.2 s(u, v) he
  have hnotsub : ¬ t ⊆ ({u, v} : Finset V) := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    have h2 : ({u, v} : Finset V).card ≤ 2 := by
      rw [Finset.card_pair huv]
    have ht4 := ht.card_eq
    omega
  obtain ⟨c, hct, hcuv⟩ := Finset.not_subset.mp hnotsub
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcuv
  obtain ⟨hcu, hcv⟩ := hcuv
  have hsub : t.erase c ⊆ G.neighborFinset c := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxc, hxt⟩ := hx
    rw [SimpleGraph.mem_neighborFinset]
    have hadj : (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj c x :=
      ht.isClique (Finset.mem_coe.mpr hct) (Finset.mem_coe.mpr hxt) (Ne.symm hxc)
    rw [SimpleGraph.sup_adj] at hadj
    rcases hadj with hGadj | hnew
    · exact hGadj
    · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff] at hnew
      obtain ⟨heq, -⟩ := hnew
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact absurd rfl hcu
      · exact absurd rfl hcv
  have hcard3 : (t.erase c).card = 3 := by
    have := Finset.card_erase_of_mem hct
    have ht4 := ht.card_eq
    omega
  calc 3 = (t.erase c).card := hcard3.symm
    _ ≤ (G.neighborFinset c).card := Finset.card_le_card hsub
    _ = G.degree c := SimpleGraph.card_neighborFinset_eq_degree G c
    _ ≤ G.maxDegree := SimpleGraph.degree_le_maxDegree G c
