import AFTD.Prelude
import AFTD.Kb.Tcs.MaxDegreeLeTwoExistsRichNeighborFiveColoring
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring

/-!
# subcubic_isAcyclic_exists_leaf_edge_dist_two_le_four

Topic: graphs   Node: d1016440b050

Provenance: helper lemma. step towards subcubic_isAcyclic_exists_rich_neighbor_five_coloring

In any finite forest of maximum degree at most 3 with at least one edge, there exists a leaf edge e (one endpoint having degree 1) with at most 4 edges at distance ≤ 2 in the line graph.
-/

/-- In any finite acyclic simple graph of maximum degree at most 3 with at least one edge, there exists an edge incident to a leaf vertex having at most 4 edges at distance 1 or 2 from it in the line graph. -/
theorem subcubic_isAcyclic_exists_leaf_edge_dist_two_le_four {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 3) (hforest : G.IsAcyclic)
    (hne : G.edgeFinset.Nonempty) :
    ∃ (e : G.edgeSet) (v : V), v ∈ e.val ∧ G.degree v = 1 ∧
      ((Finset.univ.erase e).filter (fun f : G.edgeSet =>
        G.lineGraph.Adj e f ∨ ∃ g : G.edgeSet, G.lineGraph.Adj g e ∧ G.lineGraph.Adj g f)).card ≤ 4 := by
  have _hinst := @maxDegree_le_two_exists_rich_neighbor_five_coloring_decRelLineGraphAdj V
  clear _hinst
  have _howner := @maxDegree_le_two_exists_rich_neighbor_five_coloring V
  clear _howner
  classical
  have hV : Nonempty V := by
    obtain ⟨e, he⟩ := hne
    rw [SimpleGraph.mem_edgeFinset] at he
    exact Sym2.inductionOn e (fun a b _ => ⟨a⟩) (SimpleGraph.not_isDiag_of_mem_edgeSet (G := G) he)
  obtain ⟨v0, vk, p, hp, hmax⟩ :=
    @SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length V G hV (Finite.of_fintype G.edgeSet)
  have hK1 : 1 ≤ p.length := by
    obtain ⟨e, he⟩ := hne
    rw [SimpleGraph.mem_edgeFinset] at he
    refine Sym2.inductionOn e (f := fun e => e ∈ G.edgeSet → 1 ≤ p.length) ?_ he
    intro a b hmem
    have hab : G.Adj a b := (SimpleGraph.mem_edgeSet G).mp hmem
    have hpth : hab.toWalk.IsPath := SimpleGraph.Walk.IsPath.of_adj hab
    have h := hmax a b hab.toWalk hpth
    simpa using h
  have hnil : ¬ p.Nil := by
    rw [← SimpleGraph.Walk.length_eq_zero_iff]; omega
  have hp_tail : p.tail.IsPath := hp.tail
  have hadj : G.Adj v0 p.snd := p.adj_snd hnil
  have hdecomp : p.support = v0 :: p.tail.support := by
    conv_lhs => rw [← SimpleGraph.Walk.cons_tail_eq p hnil]
    rw [SimpleGraph.Walk.support_cons]
  have hsupp_tail_of : ∀ {w : V}, w ∈ p.support → w ≠ v0 → w ∈ p.tail.support := by
    intro w hw hwv0
    rw [hdecomp] at hw
    rcases List.mem_cons.mp hw with h | h
    · exact absurd h hwv0
    · exact h
  have start_leaf : ∀ {a b : V} (r : G.Walk a b), r.IsPath → r.length = p.length → G.degree a = 1 := by
    intro a b r hr hrlen
    have hrnil : ¬ r.Nil := by rw [← SimpleGraph.Walk.length_eq_zero_iff]; omega
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨r.snd, r.adj_snd hrnil, fun w hw => ?_⟩
    by_cases hmem : w ∈ r.support
    · exact hforest.eq_snd_of_adj_start hr hw hmem
    · exfalso
      have hp' : (r.cons hw.symm).IsPath := hr.cons hmem
      have hlt := hmax w b (r.cons hw.symm) hp'
      rw [SimpleGraph.Walk.length_cons, hrlen] at hlt
      omega
  have deg_v0 : G.degree v0 = 1 := start_leaf p hp rfl
  have leaf_offpath : ∀ w : V, G.Adj p.snd w → w ∉ p.support → G.degree w = 1 := by
    intro w hwu hwsupp
    have hwt : w ∉ p.tail.support := fun h => hwsupp (by rw [hdecomp]; exact List.mem_cons_of_mem _ h)
    have hpth : (p.tail.cons hwu.symm).IsPath := hp_tail.cons hwt
    have hlen : (p.tail.cons hwu.symm).length = p.length := by
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_tail]; omega
    exact start_leaf (p.tail.cons hwu.symm) hpth hlen
  have onpath_eq : ∀ w : V, G.Adj p.snd w → w ∈ p.tail.support → w = p.tail.snd := by
    intro w hwu hwt
    exact hforest.eq_snd_of_adj_start hp_tail hwu hwt
  have hmemU : ∀ w, w ∈ (G.neighborFinset p.snd).erase v0 ↔ w ≠ v0 ∧ G.Adj p.snd w := by
    intro w; rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  have pairwise : ∀ w1 ∈ (G.neighborFinset p.snd).erase v0, ∀ w2 ∈ (G.neighborFinset p.snd).erase v0,
      w1 ≠ w2 → G.degree w1 = 1 ∨ G.degree w2 = 1 := by
    intro w1 h1 w2 h2 hne12
    obtain ⟨h1v, hadj1⟩ := (hmemU w1).mp h1
    obtain ⟨h2v, hadj2⟩ := (hmemU w2).mp h2
    by_cases hsup1 : w1 ∈ p.tail.support
    · by_cases hsup2 : w2 ∈ p.tail.support
      · exact absurd (by rw [onpath_eq w1 hadj1 hsup1, onpath_eq w2 hadj2 hsup2]) hne12
      · right; exact leaf_offpath w2 hadj2 (fun h => hsup2 (hsupp_tail_of h h2v))
    · left; exact leaf_offpath w1 hadj1 (fun h => hsup1 (hsupp_tail_of h h1v))
  let e0 : G.edgeSet := ⟨s(v0, p.snd), (SimpleGraph.mem_edgeSet G).mpr hadj⟩
  have he0v : (e0 : Sym2 V) = s(v0, p.snd) := rfl
  have hinc_v0 : ∀ f : G.edgeSet, v0 ∈ (f : Sym2 V) → f = e0 := by
    intro f hf
    have hcard : (G.incidenceFinset v0).card = 1 := by
      rw [G.card_incidenceFinset_eq_degree]; exact deg_v0
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
    have hxe : (e0 : Sym2 V) ∈ G.incidenceFinset v0 := by
      rw [SimpleGraph.mem_incidenceFinset]; exact ⟨e0.2, by rw [he0v]; exact Sym2.mem_mk_left _ _⟩
    rw [hx] at hxe
    simp only [Finset.mem_singleton] at hxe
    have hfmem : (f : Sym2 V) ∈ G.incidenceFinset v0 := by
      rw [SimpleGraph.mem_incidenceFinset]; exact ⟨f.2, hf⟩
    rw [hx] at hfmem
    simp only [Finset.mem_singleton] at hfmem
    exact Subtype.ext (hfmem.trans hxe.symm)
  have share_e0 : ∀ g : G.edgeSet, (∃ x, x ∈ (e0 : Sym2 V) ∧ x ∈ (g : Sym2 V)) → g ≠ e0 → p.snd ∈ (g : Sym2 V) := by
    intro g ⟨x, hxe0, hxg⟩ hge
    have hx : x = v0 ∨ x = p.snd := by rw [he0v] at hxe0; exact Sym2.mem_iff.mp hxe0
    rcases hx with rfl | rfl
    · exact absurd (hinc_v0 g hxg) hge
    · exact hxg
  have incidence_step : ∀ f : G.edgeSet, p.snd ∈ (f : Sym2 V) → f ≠ e0 →
      ∃ w ∈ (G.neighborFinset p.snd).erase v0, w ∈ (f : Sym2 V) := by
    intro f hps hfe
    refine ⟨Sym2.Mem.other hps, ?_, Sym2.other_mem hps⟩
    have hadj' : G.Adj p.snd (Sym2.Mem.other hps) := by
      have hmem : s(p.snd, Sym2.Mem.other hps) ∈ G.edgeSet := by
        rw [Sym2.other_spec hps]; exact f.2
      exact (SimpleGraph.mem_edgeSet G).mp hmem
    have hne : Sym2.Mem.other hps ≠ v0 := by
      intro h
      apply hfe; apply Subtype.ext
      rw [← Sym2.other_spec hps, h, he0v]; exact Sym2.eq_swap
    exact (hmemU _).mpr ⟨hne, hadj'⟩
  have cover : ∀ f : G.edgeSet, f ≠ e0 →
      (G.lineGraph.Adj e0 f ∨ ∃ g : G.edgeSet, G.lineGraph.Adj g e0 ∧ G.lineGraph.Adj g f) →
      ∃ w ∈ (G.neighborFinset p.snd).erase v0, w ∈ (f : Sym2 V) := by
    intro f hfe hdist
    rcases hdist with h1 | ⟨g, hg1, hg2⟩
    · obtain ⟨_, x, hx0, hxf⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp h1
      exact incidence_step f (share_e0 f ⟨x, hx0, hxf⟩ hfe) hfe
    · obtain ⟨hge, x, hx0, hxg⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp hg1
      obtain ⟨_, y, hyg, hyf⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp hg2
      have hpsg : p.snd ∈ (g : Sym2 V) := share_e0 g ⟨x, hxg, hx0⟩ hge
      have hspec : s(p.snd, Sym2.Mem.other hpsg) = (g : Sym2 V) := Sym2.other_spec hpsg
      have hy : y = p.snd ∨ y = Sym2.Mem.other hpsg := by
        rw [← hspec] at hyg; exact Sym2.mem_iff.mp hyg
      rcases hy with rfl | rfl
      · exact incidence_step f hyf hfe
      · have hadj' : G.Adj p.snd (Sym2.Mem.other hpsg) := by
          have hmem : s(p.snd, Sym2.Mem.other hpsg) ∈ G.edgeSet := by
            rw [hspec]; exact g.2
          exact (SimpleGraph.mem_edgeSet G).mp hmem
        have hne : Sym2.Mem.other hpsg ≠ v0 := by
          intro h
          apply hge; apply Subtype.ext
          rw [← hspec, h, he0v]; exact Sym2.eq_swap
        exact ⟨_, (hmemU _).mpr ⟨hne, hadj'⟩, hyf⟩
  have hsum : ∑ w ∈ (G.neighborFinset p.snd).erase v0, G.degree w ≤ 4 := by
    have hHcard : (((G.neighborFinset p.snd).erase v0).filter (fun w => 2 ≤ G.degree w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      by_contra hab
      rcases pairwise a ha.1 b hb.1 hab with h | h <;> omega
    have hUcard : ((G.neighborFinset p.snd).erase v0).card ≤ 2 := by
      have hmem : v0 ∈ G.neighborFinset p.snd := by
        rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm
      rw [Finset.card_erase_of_mem hmem, G.card_neighborFinset_eq_degree]
      have := G.degree_le_maxDegree p.snd
      omega
    have hpart : (((G.neighborFinset p.snd).erase v0).filter (fun w => 2 ≤ G.degree w)).card
        + (((G.neighborFinset p.snd).erase v0).filter (fun w => ¬ 2 ≤ G.degree w)).card
        = ((G.neighborFinset p.snd).erase v0).card := Finset.card_filter_add_card_filter_not _
    calc ∑ w ∈ (G.neighborFinset p.snd).erase v0, G.degree w
        ≤ ∑ w ∈ (G.neighborFinset p.snd).erase v0, (1 + if 2 ≤ G.degree w then 2 else 0) :=
          Finset.sum_le_sum (fun w _ => by
            have := G.degree_le_maxDegree w
            split_ifs <;> omega)
      _ = ((G.neighborFinset p.snd).erase v0).card
          + 2 * (((G.neighborFinset p.snd).erase v0).filter (fun w => 2 ≤ G.degree w)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.sum_filter,
            Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 := by omega
  refine ⟨e0, v0, Sym2.mem_mk_left _ _, deg_v0, ?_⟩
  calc _ ≤ (((G.neighborFinset p.snd).erase v0).biUnion (fun w => G.incidenceFinset w)).card := by
        apply Finset.card_le_card_of_injOn (fun f : G.edgeSet => (f : Sym2 V))
        · intro f hf
          have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
          have hfe : f ≠ e0 := (Finset.mem_erase.mp hf'.1).1
          obtain ⟨w, hw, hwf⟩ := cover f hfe hf'.2
          exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
            ⟨w, hw, (SimpleGraph.mem_incidenceFinset G w _).mpr ⟨f.2, hwf⟩⟩)
        · intro a _ b _ h
          exact Subtype.ext h
    _ ≤ ∑ w ∈ (G.neighborFinset p.snd).erase v0, (G.incidenceFinset w).card := Finset.card_biUnion_le
    _ = ∑ w ∈ (G.neighborFinset p.snd).erase v0, G.degree w := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        exact G.card_incidenceFinset_eq_degree w
    _ ≤ 4 := hsum
