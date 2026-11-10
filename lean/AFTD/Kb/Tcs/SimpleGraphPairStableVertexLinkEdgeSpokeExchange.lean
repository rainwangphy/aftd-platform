import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets

/-!
# simple_graph_pair_stable_vertex_link_edge_spoke_exchange

Topic: graphs   Node: c575b36f0e9a

Provenance: helper lemma. Two-edge-stable triangle-packing residual; experiment 20286. The argument does not require an outside maximum packing. No novelty claim.

In a two-edge-stable graph, for every edge yz of the link at x and every neighbor w of x, another link edge meets yz and avoids w.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

private theorem in693_two_of_three {V : Type*} [DecidableEq V] (s : Finset V) (a b x : V)
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

private theorem in693_third {V : Type*} [DecidableEq V] (s : Finset V)
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

theorem simple_graph_pair_stable_vertex_link_edge_spoke_exchange (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) (y z w : Fin n) (hy : G.Adj x y) (hz : G.Adj x z) (hyz : G.Adj y z) (hw : G.Adj x w) : ∃ u v, G.Adj x u ∧ G.Adj x v ∧ G.Adj u v ∧ (u = y ∨ u = z ∨ v = y ∨ v = z) ∧ u ≠ w ∧ v ≠ w ∧ s(u,v) ≠ s(y,z) := by
  classical
  have hxy : x ≠ y := hy.ne
  have hxz : x ≠ z := hz.ne
  have hyz' : y ≠ z := hyz.ne
  have hxw : x ≠ w := hw.ne
  have he : s(y,z) ∈ G.edgeSet := hyz
  have hf : s(x,w) ∈ G.edgeSet := hw
  have hef : s(y,z) ≠ s(x,w) := by
    intro h
    have : x = y ∨ x = z := by
      have hmem : x ∈ s(y,z) := by rw [h]; simp
      simpa using hmem
    rcases this with h | h <;> aesop
  let H := G.deleteEdges {s(y,z), s(x,w)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le (G := G) {s(y,z), s(x,w)}
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
    have hs := hstable s(y,z) s(x,w) he hf hef
    change simple_graph_triangle_packing_number H = simple_graph_triangle_packing_number G at hs
    omega
  have hQG : ∀ t ∈ Q, G.IsNClique 3 t := by
    intro t ht; exact (hQH t ht).mono hHG
  have hQc := simple_graph_maximum_triangle_packing_edge_meets G Q hQG hQpair hQcard'
  have htr : G.IsNClique 3 ({y,z,x} : Finset (Fin n)) := by
    constructor
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> aesop (add safe [hy.symm, hz.symm, hyz.symm])
    · simp [hxy, hxz, hyz', Ne.symm hxy, Ne.symm hxz, Ne.symm hyz']
  obtain ⟨q, hqQ, hmeet⟩ := hQc {y,z,x} htr
  have hqcl := hQG q hqQ
  have havoid : ¬ (y ∈ q ∧ z ∈ q) ∧ ¬ (x ∈ q ∧ w ∈ q) := by
    constructor
    · intro h
      have hadj : H.Adj y z := (hQH q hqQ).isClique h.1 h.2 hyz'
      have hnot := (SimpleGraph.deleteEdges_adj.mp hadj).2
      exact hnot (by simp)
    · intro h
      have hadj : H.Adj x w := (hQH q hqQ).isClique h.1 h.2 hxw
      have hnot := (SimpleGraph.deleteEdges_adj.mp hadj).2
      exact hnot (by simp)
  have hv : ∃ v : Fin n, (v = y ∨ v = z) ∧ v ∈ q ∧ x ∈ q := by
    rcases in693_two_of_three q y z x hmeet with hyzq | hyx | hzx
    · exact False.elim (havoid.1 hyzq)
    · exact ⟨y, Or.inl rfl, hyx.1, hyx.2⟩
    · exact ⟨z, Or.inr rfl, hzx.1, hzx.2⟩
  obtain ⟨v, hveq, hvq, hxq⟩ := hv
  have hvx : v ≠ x := by rcases hveq with rfl | rfl <;> aesop
  obtain ⟨u, huq, huv, hux⟩ := in693_third q v x hqcl.card_eq hvq hxq
  have hwq : w ∉ q := fun hwq => havoid.2 ⟨hxq, hwq⟩
  have hvw : v ≠ w := fun h => hwq (h ▸ hvq)
  have huw : u ≠ w := fun h => hwq (h ▸ huq)
  have hvu : H.Adj v u := (hQH q hqQ).isClique hvq huq (Ne.symm huv)
  have hn := (SimpleGraph.deleteEdges_adj.mp hvu).2
  have hne : s(v,u) ≠ s(y,z) := by
    intro h
    apply hn
    simp [h]
  refine ⟨v,u, hqcl.isClique hxq hvq (Ne.symm hvx), hqcl.isClique hxq huq (Ne.symm hux),
    hqcl.isClique hvq huq (Ne.symm huv), ?_, hvw, huw, hne⟩
  rcases hveq with rfl | rfl <;> simp
