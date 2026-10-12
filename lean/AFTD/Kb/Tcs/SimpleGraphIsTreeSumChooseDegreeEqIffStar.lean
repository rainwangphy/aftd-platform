import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTreeCardSubTwoLeSumChooseDegreeLeChoose
import AFTD.Kb.Tcs.SimpleGraphSumChooseDegreeTwoLeChooseCardEdgeFinset
import AFTD.Kb.Tcs.SimpleGraphEqStarGraphOfForallMemEdge

/-!
# simple_graph_is_tree_sum_choose_degree_eq_iff_star

Topic: graphs   Node: eca51eec26de

Provenance: formalization of a published result. Source: arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5, equality case of the upper bound. The star K_{1,k−1} on the vertex set of T is Mathlib's starGraph r.

For a tree T on k ≥ 2 vertices, σ₂(T) = C(k−1,2) if and only if T is a star K_{1,k−1}: some vertex r is adjacent to every other vertex and there are no other edges (T = starGraph r).
-/

theorem simple_graph_is_tree_sum_choose_degree_eq_iff_star {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (hk : 2 ≤ Fintype.card V) :
    ∑ v, (G.degree v).choose 2 = (Fintype.card V - 1).choose 2 ↔
      ∃ r : V, G = SimpleGraph.starGraph r := by
  classical
  have hE : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  constructor
  · intro hsum
    -- every two distinct edges share a vertex
    have hmeet : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁ ≠ e₂ → ∃ w, w ∈ e₁ ∧ w ∈ e₂ := by
      let S := Finset.univ.sigma (fun v => (G.incidenceFinset v).powersetCard 2)
      have hS : S.card = ∑ v, (G.degree v).choose 2 := by
        rw [Finset.card_sigma]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.card_powersetCard, SimpleGraph.card_incidenceFinset_eq_degree]
      have hsub : S.image (fun p => p.2) ⊆ G.edgeFinset.powersetCard 2 := by
        intro t ht
        simp only [Finset.mem_image, S, Finset.mem_sigma, Finset.mem_univ, true_and,
          Finset.mem_powersetCard] at ht ⊢
        obtain ⟨⟨v, t⟩, ⟨hts, htc⟩, rfl⟩ := ht
        exact ⟨hts.trans (SimpleGraph.incidenceFinset_subset G v), htc⟩
      have hinj : Set.InjOn (fun p : (Σ _ : V, Finset (Sym2 V)) => p.2) S := by
        intro p hp q hq hpq
        simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ, true_and,
          Finset.mem_powersetCard, S] at hp hq
        obtain ⟨v, t⟩ := p
        obtain ⟨w, t'⟩ := q
        simp only at hpq hp hq
        subst hpq
        by_cases hvw : v = w
        · subst hvw; rfl
        · exfalso
          obtain ⟨e₁, e₂, hne, rfl⟩ := Finset.card_eq_two.1 hp.2
          have h1v := hp.1 (Finset.mem_insert_self _ _)
          have h2v := hp.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          have h1w := hq.1 (Finset.mem_insert_self _ _)
          have h2w := hq.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          rw [SimpleGraph.mem_incidenceFinset] at h1v h2v h1w h2w
          apply hne
          have key : ∀ e ∈ G.incidenceSet v, e ∈ G.incidenceSet w → e = s(v, w) := by
            intro e hev hew
            exact (Sym2.mem_and_mem_iff hvw).1 ⟨hev.2, hew.2⟩
          rw [key _ h1v h1w, key _ h2v h2w]
      have hcard : (S.image (fun p => p.2)).card = (G.edgeFinset.powersetCard 2).card := by
        rw [Finset.card_image_of_injOn hinj, hS, hsum, Finset.card_powersetCard]
        congr 1
        omega
      have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
      intro e₁ he₁ e₂ he₂ hne
      have hmem : ({e₁, e₂} : Finset (Sym2 V)) ∈ G.edgeFinset.powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair hne⟩
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl <;> simpa
      rw [← heq] at hmem
      simp only [Finset.mem_image, S, Finset.mem_sigma, Finset.mem_univ, true_and,
        Finset.mem_powersetCard] at hmem
      obtain ⟨⟨v, t⟩, ⟨hts, -⟩, rfl⟩ := hmem
      have h1 := hts (Finset.mem_insert_self _ _)
      have h2 := hts (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [SimpleGraph.mem_incidenceFinset] at h1 h2
      exact ⟨v, h1.2, h2.2⟩
    -- an edge xy
    obtain ⟨x, y, hxy⟩ : ∃ x y, G.Adj x y := by
      obtain ⟨x, y, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
      obtain ⟨p⟩ := hT.1.preconnected x y
      cases p with
      | nil => exact absurd rfl hne
      | cons h _ => exact ⟨_, _, h⟩
    by_cases hx : ∀ e ∈ G.edgeSet, x ∈ e
    · exact ⟨x, simple_graph_eq_starGraph_of_forall_mem_edge G hT.1 x hx⟩
    push Not at hx
    obtain ⟨e₁, he₁, hxe₁⟩ := hx
    by_cases hy : ∀ e ∈ G.edgeSet, y ∈ e
    · exact ⟨y, simple_graph_eq_starGraph_of_forall_mem_edge G hT.1 y hy⟩
    push Not at hy
    obtain ⟨e₂, he₂, hye₂⟩ := hy
    -- e₁ = s(y, z), e₂ = s(x, z'), and z = z'
    have hxy' : s(x, y) ∈ G.edgeSet := hxy
    obtain ⟨w₁, hw₁a, hw₁b⟩ := hmeet _ hxy' _ he₁ (fun h => hxe₁ (h ▸ Sym2.mem_mk_left x y))
    obtain ⟨w₂, hw₂a, hw₂b⟩ := hmeet _ hxy' _ he₂ (fun h => hye₂ (h ▸ Sym2.mem_mk_right x y))
    rw [Sym2.mem_iff] at hw₁a hw₂a
    have hw₁ : w₁ = y := hw₁a.resolve_left (fun h => hxe₁ (h ▸ hw₁b))
    have hw₂ : w₂ = x := hw₂a.resolve_right (fun h => hye₂ (h ▸ hw₂b))
    subst hw₁ hw₂
    obtain ⟨z, rfl⟩ := (Sym2.mem_iff_exists.1 hw₁b)
    obtain ⟨z', rfl⟩ := (Sym2.mem_iff_exists.1 hw₂b)
    have hyz : G.Adj w₁ z := he₁
    have hxz' : G.Adj w₂ z' := he₂
    have hne12 : s(w₁, z) ≠ s(w₂, z') := fun h =>
      hxe₁ (by rw [h]; exact Sym2.mem_mk_left _ _)
    obtain ⟨w₃, hw₃a, hw₃b⟩ := hmeet _ he₁ _ he₂ hne12
    have hzz : z = z' := by
      rcases Sym2.mem_iff.1 hw₃a with h | h
      · exact absurd (h ▸ hw₃b) hye₂
      · rw [h] at hw₃b
        rcases Sym2.mem_iff.1 hw₃b with h' | h'
        · exact absurd (show w₂ ∈ s(w₁, z) by rw [h']; exact Sym2.mem_mk_right _ _) hxe₁
        · exact h'
    subst hzz
    -- triangle w₂ - w₁ - z contradicts acyclicity: s(w₂, z) is a bridge
    exfalso
    have hbr := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hT.2) hxz'
    rw [SimpleGraph.isBridge_iff] at hbr
    apply hbr
    have h1 : (G.deleteEdges {s(w₂, z)}).Adj w₂ w₁ := by
      simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
      refine ⟨hxy, fun h => ?_⟩
      rcases Sym2.eq_iff.1 h with ⟨-, h'⟩ | ⟨h', h''⟩
      · exact G.ne_of_adj hyz h'
      · exact G.ne_of_adj hxy h''.symm
    have h2 : (G.deleteEdges {s(w₂, z)}).Adj w₁ z := by
      simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
      refine ⟨hyz, fun h => ?_⟩
      rcases Sym2.eq_iff.1 h with ⟨h', -⟩ | ⟨h', -⟩
      · exact G.ne_of_adj hxy h'.symm
      · exact G.ne_of_adj hyz h'
    exact h1.reachable.trans h2.reachable
  · rintro ⟨r, rfl⟩
    have hc : (SimpleGraph.starGraph r).degree r = Fintype.card V - 1 := by
      convert SimpleGraph.degree_starGraph_center (r := r)
    have ho : ∀ v, v ≠ r → (SimpleGraph.starGraph r).degree v = 1 := fun v hv => by
      convert SimpleGraph.degree_starGraph_of_ne_center hv
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), hc,
      Finset.sum_eq_zero fun v hv => by rw [ho v (Finset.ne_of_mem_erase hv)]; rfl]
    simp
