import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets

/-!
# simple_graph_pair_stable_vertex_link_not_four_cycle

Topic: graphs   Node: 3ac571cd70ee

Provenance: helper lemma. Two-edge-stable triangle-packing residual; experiment 20286. No novelty claim.

In a two-edge-stable graph, the graph induced by the neighborhood of any vertex cannot be exactly a four-cycle after isolated vertices are discarded.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

private theorem in693_cycle_two_of_three {V : Type*} [DecidableEq V] (s : Finset V) (a b x : V)
    (h : 2 ≤ (s ∩ {a,b,x}).card) :
    (a ∈ s ∧ b ∈ s) ∨ (a ∈ s ∧ x ∈ s) ∨ (b ∈ s ∧ x ∈ s) := by
  classical
  by_contra hn
  have hle : (s ∩ {a,b,x}).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu hv
    aesop
  omega

private theorem in693_cycle_third {V : Type*} [DecidableEq V] (s : Finset V)
    (a x : V) (hcard : s.card = 3) (ha : a ∈ s) (hx : x ∈ s) :
    ∃ y ∈ s, y ≠ a ∧ y ≠ x := by
  classical
  by_contra hn
  have hsub : s ⊆ {a,x} := by
    intro y hy
    simp only [not_exists, not_and] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hn2
    exact hn y hy (by aesop) (by aesop)
  have hc := Finset.card_le_card hsub
  have htwo := Finset.card_le_two (a := a) (b := x)
  omega

theorem simple_graph_pair_stable_vertex_link_not_four_cycle (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) (a b c d : Fin n) (hdist : ({a,b,c,d} : Finset (Fin n)).card = 4) : (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.Adj x v)) ≠ ({s(a,b),s(b,c),s(c,d),s(d,a)} : Finset (Sym2 (Fin n))) := by
  classical
  intro hlinkeq
  have hab : a ≠ b := by
    intro h
    have hs : ({a,b,c,d} : Finset (Fin n)) ⊆ {a,c,d} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := c) (c := d)
    omega
  have hac : a ≠ c := by
    intro h
    have hs : ({a,b,c,d} : Finset (Fin n)) ⊆ {a,b,d} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := d)
    omega
  have had : a ≠ d := by
    intro h
    have hs : ({a,b,c,d} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  have hbc : b ≠ c := by
    intro h
    have hs : ({a,b,c,d} : Finset (Fin n)) ⊆ {a,b,d} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := d)
    omega
  have hbd : b ≠ d := by
    intro h
    have hs : ({a,b,c,d} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  have hcd : c ≠ d := by
    intro h
    have hs : ({a,b,c,d} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  have hlink : ∀ u v, G.Adj x u → G.Adj x v → G.Adj u v →
      s(u,v) ∈ ({s(a,b),s(b,c),s(c,d),s(d,a)} : Finset (Sym2 (Fin n))) := by
    intro u v hxu hxv huv
    have hm : s(u,v) ∈ G.edgeFinset.filter (fun e => ∀ w ∈ e, G.Adj x w) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact SimpleGraph.mem_edgeFinset.mpr huv
      · intro w hw
        have hw' : w = u ∨ w = v := by simpa using hw
        rcases hw' with rfl | rfl <;> assumption
    rwa [hlinkeq] at hm
  have hE : ∀ u v, s(u,v) ∈ ({s(a,b),s(b,c),s(c,d),s(d,a)} : Finset (Sym2 (Fin n))) →
      G.Adj u v ∧ G.Adj x u ∧ G.Adj x v := by
    intro u v h
    have hm : s(u,v) ∈ G.edgeFinset.filter (fun e => ∀ w ∈ e, G.Adj x w) := by rwa [hlinkeq]
    obtain ⟨he,hx⟩ := Finset.mem_filter.mp hm
    exact ⟨SimpleGraph.mem_edgeFinset.mp he, hx u (by simp), hx v (by simp)⟩
  have habg := hE a b (by simp)
  have hbcg := hE b c (by simp)
  have hcdg := hE c d (by simp)
  have hdag := hE d a (by simp)
  have hxa : x ≠ a := habg.2.1.ne
  have hxb : x ≠ b := habg.2.2.ne
  have hxc : x ≠ c := hbcg.2.2.ne
  have hxd : x ≠ d := hcdg.2.2.ne
  have he : s(a,b) ∈ G.edgeSet := habg.1
  have hf : s(b,c) ∈ G.edgeSet := hbcg.1
  have hef : s(a,b) ≠ s(b,c) := by simp [Sym2.eq_iff, hab, hbc, hac]
  let H := G.deleteEdges {s(a,b), s(b,c)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le (G := G) {s(a,b), s(b,c)}
  let A : Set ℕ := {k | ∃ Q : Finset (Finset (Fin n)),
    (∀ t ∈ Q, H.IsNClique 3 t) ∧
    (Q : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ Q.card = k}
  have hne : A.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  have hbdd : BddAbove A := by
    refine ⟨Fintype.card (Finset (Fin n)), ?_⟩
    rintro k ⟨Q, _, _, rfl⟩
    exact Finset.card_le_univ Q
  obtain ⟨Q, hQH, hQpair, hQcard⟩ := Nat.sSup_mem hne hbdd
  have hQcard' : Q.card = simple_graph_triangle_packing_number G := by
    change Q.card = simple_graph_triangle_packing_number H at hQcard
    have hs := hstable s(a,b) s(b,c) he hf hef
    change simple_graph_triangle_packing_number H = simple_graph_triangle_packing_number G at hs
    omega
  have hQG : ∀ t ∈ Q, G.IsNClique 3 t := by
    intro t ht; exact (hQH t ht).mono hHG
  have hQc := simple_graph_maximum_triangle_packing_edge_meets G Q hQG hQpair hQcard'
  have havoid : ∀ t ∈ Q, ¬ (a ∈ t ∧ b ∈ t) ∧ ¬ (b ∈ t ∧ c ∈ t) := by
    intro t ht
    constructor
    · intro h
      have hadj : H.Adj a b := (hQH t ht).isClique h.1 h.2 hab
      exact (SimpleGraph.deleteEdges_adj.mp hadj).2 (by simp)
    · intro h
      have hadj : H.Adj b c := (hQH t ht).isClique h.1 h.2 hbc
      exact (SimpleGraph.deleteEdges_adj.mp hadj).2 (by simp)
  have hextract : ∀ q ∈ Q, ∀ v, x ∈ q → v ∈ q → v ≠ x →
      ∃ u ∈ q, u ≠ v ∧ u ≠ x ∧ G.Adj x u ∧ H.Adj v u := by
    intro q hq v hxq hvq hvx
    have hqcl := hQG q hq
    obtain ⟨u,huq,huv,hux⟩ := in693_cycle_third q v x hqcl.card_eq hvq hxq
    exact ⟨u,huq,huv,hux,hqcl.isClique hxq huq (Ne.symm hux),
      (hQH q hq).isClique hvq huq (Ne.symm huv)⟩
  have hno_b : ∀ q ∈ Q, ¬ (x ∈ q ∧ b ∈ q) := by
    intro q hq h
    obtain ⟨u,huq,hub,hux,hxu,hbu⟩ := hextract q hq b h.1 h.2 (Ne.symm hxb)
    have hm := hlink b u habg.2.2 hxu (hHG hbu)
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hm
    have hu : u = a ∨ u = c := by aesop
    have hn := (SimpleGraph.deleteEdges_adj.mp hbu).2
    rcases hu with rfl | rfl
    · apply hn; simp [Sym2.eq_iff]
    · apply hn; simp
  have hba : G.Adj b a := habg.1.symm
  have hay : G.Adj a x := habg.2.1.symm
  have hby : G.Adj b x := habg.2.2.symm
  have hcb : G.Adj c b := hbcg.1.symm
  have hcy : G.Adj c x := hbcg.2.2.symm
  have htri1 : G.IsNClique 3 ({x,a,b} : Finset (Fin n)) := by
    constructor
    · intro u hu v hv huv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        aesop
    · simp [hxa,hxb,hab,Ne.symm hxa,Ne.symm hxb,Ne.symm hab]
  have htri2 : G.IsNClique 3 ({x,b,c} : Finset (Fin n)) := by
    constructor
    · intro u hu v hv huv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        aesop
    · simp [hxb,hxc,hbc,Ne.symm hxb,Ne.symm hxc,Ne.symm hbc]
  obtain ⟨q1,hq1,hm1⟩ := hQc {x,a,b} htri1
  obtain ⟨q2,hq2,hm2⟩ := hQc {x,b,c} htri2
  have hx1a : x ∈ q1 ∧ a ∈ q1 := by
    rcases in693_cycle_two_of_three q1 x a b hm1 with h | h | h
    · exact h
    · exact False.elim (hno_b q1 hq1 h)
    · exact False.elim ((havoid q1 hq1).1 h)
  have hx2c : x ∈ q2 ∧ c ∈ q2 := by
    rcases in693_cycle_two_of_three q2 x b c hm2 with h | h | h
    · exact False.elim (hno_b q2 hq2 h)
    · exact h
    · exact False.elim ((havoid q2 hq2).2 h)
  have hd1 : d ∈ q1 := by
    obtain ⟨u,huq,hua,hux,hxu,hau⟩ := hextract q1 hq1 a hx1a.1 hx1a.2 (Ne.symm hxa)
    have hm := hlink a u habg.2.1 hxu (hHG hau)
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hm
    have hu : u = b ∨ u = d := by aesop
    rcases hu with rfl | rfl
    · exact False.elim ((havoid q1 hq1).1 ⟨hx1a.2,huq⟩)
    · exact huq
  have hd2 : d ∈ q2 := by
    obtain ⟨u,huq,huc,hux,hxu,hcu⟩ := hextract q2 hq2 c hx2c.1 hx2c.2 (Ne.symm hxc)
    have hm := hlink c u hbcg.2.2 hxu (hHG hcu)
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hm
    have hu : u = b ∨ u = d := by aesop
    rcases hu with rfl | rfl
    · exact False.elim ((havoid q2 hq2).2 ⟨huq,hx2c.2⟩)
    · exact huq
  have hqne : q1 ≠ q2 := by
    intro h; subst q2
    have hs : ({x,a,c,d} : Finset (Fin n)) ⊆ q1 := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hx1a.1
      · exact hx1a.2
      · exact hx2c.2
      · exact hd1
    have hcard := Finset.card_le_card hs
    have hfour : ({x,a,c,d} : Finset (Fin n)).card = 4 := by
      simp [hxa,hxc,hxd,hac,had,hcd,Ne.symm hxa,Ne.symm hxc,Ne.symm hxd,Ne.symm hac,Ne.symm had,Ne.symm hcd]
    have hc := (hQG q1 hq1).card_eq
    omega
  have hs : ({x,d} : Finset (Fin n)) ⊆ q1 ∩ q2 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [Finset.mem_inter]
    rcases hv with rfl | rfl
    · exact ⟨hx1a.1,hx2c.1⟩
    · exact ⟨hd1,hd2⟩
  have hcard := Finset.card_le_card hs
  have hp := hQpair hq1 hq2 hqne
  simp [hxd] at hcard
  omega
