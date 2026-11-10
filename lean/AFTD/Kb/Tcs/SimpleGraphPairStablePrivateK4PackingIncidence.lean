import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphPairStableVertexLinkEdgeSpokeExchange
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets

/-!
# simple_graph_pair_stable_private_k4_packing_incidence

Topic: graphs   Node: 61dccac117f0

Provenance: helper lemma. Private-witness exchange in the internal-anchor branch of the triangle-packing campaign; compare https://arxiv.org/abs/2001.00257, Section 3.

Let a maximum packing in a two-edge-stable graph contain abc, with a and b private to that packing triangle. If abcx is a four-clique whose x-spokes are unused by the packing, then x occurs in at least two packing triangles, c occurs in at least three, and the packing contains at least five triangles.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

lemma in694inc_private_swap_impossible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) (p t u : Finset V)
    (htri : ∀ q ∈ P, G.IsNClique 3 q)
    (hdisj : (P : Set (Finset V)).Pairwise (fun q r => (q ∩ r).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G) (hp : p ∈ P)
    (ht : G.IsNClique 3 t) (hu : G.IsNClique 3 u)
    (htu : (t ∩ u).card ≤ 1)
    (htpriv : ∀ q ∈ P, q ≠ p → (t ∩ q).card ≤ 1)
    (hupriv : ∀ q ∈ P, q ≠ p → (u ∩ q).card ≤ 1) : False := by
  classical
  let R := P.erase p
  have hRt : t ∉ R := by
    intro htR
    have htP := Finset.mem_of_mem_erase htR
    have htp := (Finset.ne_of_mem_erase htR)
    have h := htpriv t htP htp
    rw [Finset.inter_self, ht.card_eq] at h
    omega
  have hRu : u ∉ R := by
    intro huR
    have huP := Finset.mem_of_mem_erase huR
    have hup := (Finset.ne_of_mem_erase huR)
    have h := hupriv u huP hup
    rw [Finset.inter_self, hu.card_eq] at h
    omega
  have htu' : t ≠ u := by
    intro h; subst u
    rw [Finset.inter_self, ht.card_eq] at htu
    omega
  let Q := insert t (insert u R)
  have hQcl : ∀ q ∈ Q, G.IsNClique 3 q := by
    intro q hq
    simp only [Q, Finset.mem_insert] at hq
    rcases hq with rfl | rfl | hq
    · exact ht
    · exact hu
    · exact htri q (Finset.mem_of_mem_erase hq)
  have hQpair : (Q : Set (Finset V)).Pairwise (fun q r => (q ∩ r).card ≤ 1) := by
    have hRpair : (R : Set (Finset V)).Pairwise (fun q r => (q ∩ r).card ≤ 1) := by
      intro q hq r hr hne
      exact hdisj (Finset.mem_of_mem_erase hq) (Finset.mem_of_mem_erase hr) hne
    change ((insert t (insert u R) : Finset (Finset V)) : Set (Finset V)).Pairwise _
    rw [Finset.coe_insert, Finset.coe_insert]
    apply Set.Pairwise.insert
    · apply Set.Pairwise.insert hRpair
      intro q hq _
      have h := hupriv q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)
      exact ⟨h, by rw [Finset.inter_comm]; exact h⟩
    · intro q hq _
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · exact ⟨htu, by rw [Finset.inter_comm]; exact htu⟩
      · have h := htpriv q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)
        exact ⟨h, by rw [Finset.inter_comm]; exact h⟩
  have hQcard : Q.card = P.card + 1 := by
    have ht' : t ∉ insert u R := by simp [htu', hRt]
    have hp_pos : 0 < P.card := Finset.card_pos.mpr ⟨p, hp⟩
    rw [show Q = insert t (insert u (P.erase p)) by rfl,
      Finset.card_insert_of_notMem ht', Finset.card_insert_of_notMem hRu,
      Finset.card_erase_of_mem hp]
    omega
  have hbdd : BddAbove {n | ∃ T : Finset (Finset V), (∀ a ∈ T, G.IsNClique 3 a) ∧
      (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n} := by
    refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
    rintro n ⟨T, -, -, rfl⟩
    exact Finset.card_le_univ T
  have hle : Q.card ≤ simple_graph_triangle_packing_number G := by
    unfold simple_graph_triangle_packing_number
    exact le_csSup hbdd ⟨Q, hQcl, hQpair, rfl⟩
  omega

lemma in694inc_private_pair_card_le_one {V : Type*} [DecidableEq V]
    (q : Finset V) (a b y : V) (ha : a ∉ q) (hb : b ∉ q) :
    (({a,b,y} : Finset V) ∩ q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
  aesop

lemma in694inc_private_free_pair_card_le_one {V : Type*} [DecidableEq V]
    (q : Finset V) (a c x : V) (ha : a ∉ q) (hcx : ¬ (c ∈ q ∧ x ∈ q)) :
    (({a,c,x} : Finset V) ∩ q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
  aesop

lemma in694inc_private_k4_codegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) (a b c x : V)
    (htri : ∀ q ∈ P, G.IsNClique 3 q)
    (hdisj : (P : Set (Finset V)).Pairwise (fun q r => (q ∩ r).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (hp : ({a,b,c} : Finset V) ∈ P)
    (hab : G.Adj a b) (hac : G.Adj a c) (hax : G.Adj a x) (hcx : G.Adj c x)
    (hbc : b ≠ c) (hbx : b ≠ x)
    (hprivate : ∀ q ∈ P, q ≠ ({a,b,c} : Finset V) → a ∉ q ∧ b ∉ q)
    (hfreecx : ∀ q ∈ P, ¬ (c ∈ q ∧ x ∈ q)) :
    ∀ y, G.Adj a y → G.Adj b y → y = c ∨ y = x := by
  intro y hay hby
  by_contra hn
  push_neg at hn
  have hyc : y ≠ c := hn.1
  have hyx : y ≠ x := hn.2
  have hab' := hab.ne
  have hac' := hac.ne
  have hax' := hax.ne
  have hcx' := hcx.ne
  have hay' := hay.ne
  have hby' := hby.ne
  have ht : G.IsNClique 3 ({a,b,y} : Finset V) := by
    constructor
    · intro v hv w hw hvw
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> aesop (add safe [hab.symm, hay.symm, hby.symm])
    · simp [hab', hay', hby', Ne.symm hab', Ne.symm hay', Ne.symm hby']
  have hu : G.IsNClique 3 ({a,c,x} : Finset V) := by
    constructor
    · intro v hv w hw hvw
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> aesop (add safe [hac.symm, hax.symm, hcx.symm])
    · simp [hac', hax', hcx', Ne.symm hac', Ne.symm hax', Ne.symm hcx']
  have htu : (({a,b,y} : Finset V) ∩ {a,c,x}).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
    aesop
  apply in694inc_private_swap_impossible G P {a,b,c} {a,b,y} {a,c,x} htri hdisj hmax hp ht hu htu
  · intro q hq hqp
    obtain ⟨ha,hb⟩ := hprivate q hq hqp
    exact in694inc_private_pair_card_le_one q a b y ha hb
  · intro q hq hqp
    obtain ⟨ha,hb⟩ := hprivate q hq hqp
    exact in694inc_private_free_pair_card_le_one q a c x ha (hfreecx q hq)


lemma in694inc_four_distinct {V : Type*} [DecidableEq V] (a b c x : V)
    (h : ({a,b,c,x} : Finset V).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ x ∧ b ≠ c ∧ b ≠ x ∧ c ≠ x := by
  simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
    Finset.card_singleton] at h
  split_ifs at h <;> simp_all

lemma in694inc_private_k4_edge_codegree_two (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Finset (Fin n))) (a b c x : Fin n)
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (hp : ({a,b,c} : Finset (Fin n)) ∈ P)
    (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n)))
    (hprivate : ∀ q ∈ P, q ≠ ({a,b,c} : Finset (Fin n)) → a ∉ q ∧ b ∉ q)
    (hfree : ∀ v ∈ ({a,b,c} : Finset (Fin n)), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) :
    ∀ y : Fin n, G.Adj a y → G.Adj b y → y = c ∨ y = x := by
  classical
  obtain ⟨hab,hac,hax,hbc,hbx,hcx⟩ := in694inc_four_distinct a b c x hk4.card_eq
  have ha : a ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hb : b ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hc : c ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hx : x ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hadj := hk4.isClique
  have hfreecx : ∀ q ∈ P, ¬ (c ∈ q ∧ x ∈ q) := by
    intro q hq ⟨hcq,hxq⟩
    have hmem : s(x,c) ∈ finite_vertex_set_edge_encoding q := by
      simp [finite_vertex_set_edge_encoding, Sym2.mk_isDiag_iff, hxq, hcq, Ne.symm hcx]
    apply hfree c (by simp)
    exact Finset.mem_biUnion.mpr ⟨q,hq,hmem⟩
  exact in694inc_private_k4_codegree G P a b c x htri hdisj hmax hp
    (hadj ha hb hab) (hadj ha hc hac) (hadj ha hx hax) (hadj hc hx hcx) hbc hbx hprivate hfreecx

lemma in694inc_link_anchor_neighbor (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c x : Fin n)
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G)
    (hab : G.Adj a b) (hac : G.Adj a c) (hax : G.Adj a x) (hbx : G.Adj b x)
    (hcodeg : ∀ y, G.Adj a y → G.Adj b y → y = c ∨ y = x) :
    ∃ y, y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ y ≠ x ∧ G.Adj a y ∧ G.Adj x y := by
  classical
  obtain ⟨u,v, hau,hav,huv,hm,huc,hvc,hne⟩ :=
    simple_graph_pair_stable_vertex_link_edge_spoke_exchange n G a hstable b x c hab hax hbx hac
  have hub : u ≠ b := by
    intro h; subst u
    rcases hcodeg v hav huv with hvc' | hvx
    · exact hvc hvc'
    · subst v; exact hne rfl
  have hvb : v ≠ b := by
    intro h; subst v
    rcases hcodeg u hau huv.symm with huc' | hux
    · exact huc huc'
    · subst u; apply hne; exact Sym2.eq_swap
  rcases hm with h | h | h | h
  · exact (hub h).elim
  · subst u
    exact ⟨v,hav.ne.symm,hvb,hvc,huv.ne.symm,hav,huv⟩
  · exact (hvb h).elim
  · subst v
    exact ⟨u,hau.ne.symm,hub,huc,huv.ne,hau,huv.symm⟩

lemma in694inc_two_members_of_large_intersection {V : Type*} [DecidableEq V]
    (q : Finset V) (a x y : V) (ha : a ∉ q)
    (h : 2 ≤ (q ∩ ({a,x,y} : Finset V)).card) : x ∈ q ∧ y ∈ q := by
  by_contra hn
  have hle : (q ∩ ({a,x,y} : Finset V)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
    aesop
  omega

lemma in694inc_anchor_triangle_meets_other_packing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) (p : Finset V) (a x y : V)
    (htri : ∀ q ∈ P, G.IsNClique 3 q)
    (hdisj : (P : Set (Finset V)).Pairwise (fun q r => (q ∩ r).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (hp : p ∈ P) (hx : x ∉ p) (hy : y ∉ p)
    (hprivate : ∀ q ∈ P, q ≠ p → a ∉ q)
    (ht : G.IsNClique 3 ({a,x,y} : Finset V)) :
    ∃ q ∈ P, q ≠ p ∧ x ∈ q ∧ y ∈ q := by
  obtain ⟨q,hq,hmeet⟩ := simple_graph_maximum_triangle_packing_edge_meets G P htri hdisj hmax {a,x,y} ht
  have hqp : q ≠ p := by
    intro h; subst q
    have hle : (p ∩ ({a,x,y} : Finset V)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro v hv w hw
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
      aesop
    omega
  obtain ⟨hqx,hqy⟩ := in694inc_two_members_of_large_intersection q a x y (hprivate q hq hqp) hmeet
  exact ⟨q,hq,hqp,hqx,hqy⟩

lemma in694inc_distinct_packed_triangles_no_shared_pair {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (q r : Finset V) (x y : V)
    (hdisj : (P : Set (Finset V)).Pairwise (fun q r => (q ∩ r).card ≤ 1))
    (hq : q ∈ P) (hr : r ∈ P) (hqr : q ≠ r)
    (hqx : x ∈ q) (hqy : y ∈ q) (hxy : x ≠ y) : ¬ (x ∈ r ∧ y ∈ r) := by
  intro ⟨hrx,hry⟩
  have hs : ({x,y} : Finset V) ⊆ q ∩ r := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp_all
  have hcard := Finset.card_le_card hs
  have hpair := hdisj hq hr hqr
  simp [hxy] at hcard
  omega

lemma in694inc_mixed_anchor_witnesses_impossible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) (p q : Finset V) (a b x y z : V)
    (htri : ∀ r ∈ P, G.IsNClique 3 r)
    (hdisj : (P : Set (Finset V)).Pairwise (fun r s => (r ∩ s).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : q ≠ p)
    (ha : a ∈ p) (hb : b ∈ p) (hab : a ≠ b)
    (hx : x ∉ p) (hy : y ∉ p) (hz : z ∉ p) (hyz : y ≠ z)
    (hqx : x ∈ q) (hqy : y ∈ q) (hqz : z ∈ q)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hprivate : ∀ r ∈ P, r ≠ p → a ∉ r ∧ b ∉ r)
    (ht : G.IsNClique 3 ({a,x,y} : Finset V))
    (hu : G.IsNClique 3 ({b,x,z} : Finset V)) : False := by
  have htu : (({a,x,y} : Finset V) ∩ {b,x,z}).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
    aesop
  apply in694inc_private_swap_impossible G P q {a,x,y} {b,x,z} htri hdisj hmax hq ht hu htu
  · intro r hr hrq
    by_cases hrp : r = p
    · subst r
      apply Finset.card_le_one.mpr
      intro v hv w hw
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
      aesop
    · obtain ⟨har,hbr⟩ := hprivate r hr hrp
      have hxy' := in694inc_distinct_packed_triangles_no_shared_pair P q r x y hdisj hq hr (Ne.symm hrq) hqx hqy hxy
      exact in694inc_private_free_pair_card_le_one r a x y har hxy'
  · intro r hr hrq
    by_cases hrp : r = p
    · subst r
      apply Finset.card_le_one.mpr
      intro v hv w hw
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
      aesop
    · obtain ⟨har,hbr⟩ := hprivate r hr hrp
      have hxz' := in694inc_distinct_packed_triangles_no_shared_pair P q r x z hdisj hq hr (Ne.symm hrq) hqx hqz hxz
      exact in694inc_private_free_pair_card_le_one r b x z hbr hxz'

lemma in694inc_triangle_of_edges {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    G.IsNClique 3 ({a,b,c} : Finset V) := by
  constructor
  · intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      aesop (add safe [hab.symm, hac.symm, hbc.symm])
  · simp [hab.ne,hac.ne,hbc.ne]

lemma in694inc_pair_stable_private_k4_anchor_incidence (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Finset (Fin n))) (a b c x : Fin n)
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G)
    (hp : ({a,b,c} : Finset (Fin n)) ∈ P)
    (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n)))
    (hprivate : ∀ q ∈ P, q ≠ ({a,b,c} : Finset (Fin n)) → a ∉ q ∧ b ∉ q)
    (hfree : ∀ v ∈ ({a,b,c} : Finset (Fin n)), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) :
    2 ≤ (P.filter (fun q => x ∈ q)).card := by
  classical
  obtain ⟨hab,hac,hax,hbc,hbx,hcx⟩ := in694inc_four_distinct a b c x hk4.card_eq
  have ha : a ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hb : b ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hc : c ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hx : x ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hadj := hk4.isClique
  have hab' := hadj ha hb hab
  have hac' := hadj ha hc hac
  have hax' := hadj ha hx hax
  have hbc' := hadj hb hc hbc
  have hbx' := hadj hb hx hbx
  have hcodeg := in694inc_private_k4_edge_codegree_two n G P a b c x htri hdisj hmax hp hk4 hprivate hfree
  obtain ⟨y,hya,hyb,hyc,hyx,hay,hxy⟩ :=
    in694inc_link_anchor_neighbor n G a b c x hstable hab' hac' hax' hbx' hcodeg
  have hcodeg' : ∀ v, G.Adj b v → G.Adj a v → v = c ∨ v = x := by
    intro v hbv hav
    exact hcodeg v hav hbv
  obtain ⟨z,hzb,hza,hzc,hzx,hbz,hxz⟩ :=
    in694inc_link_anchor_neighbor n G b a c x hstable hab'.symm hbc' hbx' hax' hcodeg'
  have hyz : y ≠ z := by
    intro h; subst z
    rcases hcodeg y hay hbz with h | h
    · exact hyc h
    · exact hyx h
  have hxp : x ∉ ({a,b,c} : Finset (Fin n)) := by simp [Ne.symm hax, Ne.symm hbx, Ne.symm hcx]
  have hyp : y ∉ ({a,b,c} : Finset (Fin n)) := by simp [hya,hyb,hyc]
  have hzp : z ∉ ({a,b,c} : Finset (Fin n)) := by simp [hza,hzb,hzc]
  have ht := in694inc_triangle_of_edges G a x y hax' hay hxy
  have hu := in694inc_triangle_of_edges G b x z hbx' hbz hxz
  obtain ⟨q,hq,hqp,hqx,hqy⟩ := in694inc_anchor_triangle_meets_other_packing G P {a,b,c} a x y htri hdisj hmax hp hxp hyp (fun r hr hrp => (hprivate r hr hrp).1) ht
  obtain ⟨r,hr,hrp,hrx,hrz⟩ := in694inc_anchor_triangle_meets_other_packing G P {a,b,c} b x z htri hdisj hmax hp hxp hzp (fun r hr hrp => (hprivate r hr hrp).2) hu
  have hqr : q ≠ r := by
    intro h; subst r
    exact in694inc_mixed_anchor_witnesses_impossible G P {a,b,c} q a b x y z htri hdisj hmax hp hq hqp (by simp) (by simp) hab hxp hyp hzp hyz hqx hqy hrz (Ne.symm hyx) (Ne.symm hzx) hprivate ht hu
  have hs : ({q,r} : Finset (Finset (Fin n))) ⊆ P.filter (fun t => x ∈ t) := by
    intro t ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl <;> simp_all
  have hcard := Finset.card_le_card hs
  simpa [hqr] using hcard

theorem simple_graph_pair_stable_private_k4_packing_incidence (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (a b c x : Fin n) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) (hprivate : ∀ q ∈ P, q ≠ ({a,b,c} : Finset (Fin n)) → a ∉ q ∧ b ∉ q) (hfree : ∀ v ∈ ({a,b,c} : Finset (Fin n)), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) : 2 ≤ (P.filter (fun q => x ∈ q)).card ∧ 3 ≤ (P.filter (fun q => c ∈ q)).card ∧ 5 ≤ P.card := by
  classical
  obtain ⟨hab,hac,hax,hbc,hbx,hcx⟩ := in694inc_four_distinct a b c x hk4.card_eq
  have ha : a ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hb : b ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hc : c ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hx : x ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
  have hadj := hk4.isClique
  have ht := in694inc_triangle_of_edges G a b x (hadj ha hb hab) (hadj ha hx hax) (hadj hb hx hbx)
  have hcx_free : ∀ q ∈ P, ¬ (c ∈ q ∧ x ∈ q) := by
    intro q hq ⟨hcq,hxq⟩
    have hm : s(x,c) ∈ finite_vertex_set_edge_encoding q := by
      simp [finite_vertex_set_edge_encoding, Sym2.mk_isDiag_iff, hxq, hcq, Ne.symm hcx]
    exact hfree c (by simp) (Finset.mem_biUnion.mpr ⟨q,hq,hm⟩)
  let p : Finset (Fin n) := {a,b,c}
  let t : Finset (Fin n) := {a,b,x}
  let R := P.erase p
  let Q := insert t R
  have hRt : t ∉ R := by
    intro hm
    have hqP := Finset.mem_of_mem_erase hm
    have hqp := Finset.ne_of_mem_erase hm
    have hn := (hprivate t hqP hqp).1
    exact hn (by simp [t])
  have hQcl : ∀ q ∈ Q, G.IsNClique 3 q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ht
    · exact htri q (Finset.mem_of_mem_erase hq)
  have hQpair : (Q : Set (Finset (Fin n))).Pairwise (fun q r => (q ∩ r).card ≤ 1) := by
    have hRpair : (R : Set (Finset (Fin n))).Pairwise (fun q r => (q ∩ r).card ≤ 1) := by
      intro q hq r hr hne
      exact hdisj (Finset.mem_of_mem_erase hq) (Finset.mem_of_mem_erase hr) hne
    change ((insert t R : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Pairwise _
    rw [Finset.coe_insert]
    apply Set.Pairwise.insert hRpair
    intro q hq _
    obtain ⟨haq,hbq⟩ := hprivate q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)
    have h := in694inc_private_pair_card_le_one q a b x haq hbq
    exact ⟨h, by rw [Finset.inter_comm]; exact h⟩
  have hQcard : Q.card = P.card := by
    have hpos : 0 < P.card := Finset.card_pos.mpr ⟨p,hp⟩
    rw [show Q = insert t (P.erase p) by rfl, Finset.card_insert_of_notMem hRt, Finset.card_erase_of_mem hp]
    omega
  have hQmax : Q.card = simple_graph_triangle_packing_number G := hQcard.trans hmax
  have htQ : t ∈ Q := by simp [Q]
  have hcnot_t : c ∉ t := by simp [t, Ne.symm hac, Ne.symm hbc, hcx]
  have hQprivate : ∀ q ∈ Q, q ≠ t → a ∉ q ∧ b ∉ q := by
    intro q hq hqt
    have hqR : q ∈ R := (Finset.mem_insert.mp hq).resolve_left hqt
    exact hprivate q (Finset.mem_of_mem_erase hqR) (Finset.ne_of_mem_erase hqR)
  have hQfree : ∀ v ∈ t, s(c,v) ∉ Q.biUnion finite_vertex_set_edge_encoding := by
    intro v hv hm
    obtain ⟨q,hq,henc⟩ := Finset.mem_biUnion.mp hm
    have hmem : c ∈ q ∧ v ∈ q := by
      have hv : (c ∈ q ∧ v ∈ q) ∧ c ≠ v := by
        simpa [finite_vertex_set_edge_encoding, Sym2.mk_isDiag_iff] using henc
      exact hv.1
    rcases Finset.mem_insert.mp hq with rfl | hqR
    · exact hcnot_t hmem.1
    · have hqP := Finset.mem_of_mem_erase hqR
      have hqp := Finset.ne_of_mem_erase hqR
      obtain ⟨haq,hbq⟩ := hprivate q hqP hqp
      simp only [t, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact haq hmem.2
      · exact hbq hmem.2
      · exact hcx_free q hqP hmem
  have hk4' : G.IsNClique 4 ({a,b,x,c} : Finset (Fin n)) := by
    have heq : ({a,b,x,c} : Finset (Fin n)) = {a,b,c,x} := by ext v; simp; aesop
    rwa [heq]
  have hx_bound : 2 ≤ (P.filter (fun q => x ∈ q)).card :=
    in694inc_pair_stable_private_k4_anchor_incidence n G P a b c x htri hdisj hmax hstable hp hk4 hprivate hfree
  have hc_Qbound : 2 ≤ (Q.filter (fun q => c ∈ q)).card :=
    in694inc_pair_stable_private_k4_anchor_incidence n G Q a b x c hQcl hQpair hQmax hstable htQ hk4' hQprivate hQfree
  let B := P.filter (fun q => c ∈ q)
  have hpB : p ∈ B := by simp [B,p,hp]
  have hsub : Q.filter (fun q => c ∈ q) ⊆ B.erase p := by
    intro q hq
    obtain ⟨hqQ,hqc⟩ := Finset.mem_filter.mp hq
    have hqR : q ∈ R := (Finset.mem_insert.mp hqQ).resolve_left (by intro h; subst q; exact hcnot_t hqc)
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hqR, Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hqR,hqc⟩⟩
  have hBbound : 3 ≤ B.card := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hpB] at hh
    have hpos : 0 < B.card := Finset.card_pos.mpr ⟨p,hpB⟩
    omega
  have hD : Disjoint B (P.filter (fun q => x ∈ q)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hqx
    have ⟨hqP,hqc⟩ := Finset.mem_filter.mp hq
    have hqx' := (Finset.mem_filter.mp hqx).2
    exact hcx_free q hqP ⟨hqc,hqx'⟩
  have hUnion : B ∪ (P.filter (fun q => x ∈ q)) ⊆ P := by
    intro q hq
    simp only [Finset.mem_union, B, Finset.mem_filter] at hq
    aesop
  have hcard := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hD] at hcard
  exact ⟨hx_bound, hBbound, by omega⟩
