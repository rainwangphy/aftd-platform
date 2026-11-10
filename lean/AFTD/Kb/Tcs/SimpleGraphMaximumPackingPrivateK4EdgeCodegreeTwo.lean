import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_maximum_packing_private_k4_edge_codegree_two

Topic: graphs   Node: 6be8716dc474

Provenance: helper lemma. Private-witness exchange in the internal-anchor branch of the triangle-packing campaign; compare https://arxiv.org/abs/2001.00257, Section 3.

If a triangle in a maximum edge-disjoint triangle packing has two vertices private to that triangle and extends to a four-clique whose three new edges are not used by the packing, its edge between the two private vertices has exactly the other two clique vertices as common neighbors.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

lemma in694_private_swap_impossible {V : Type*} [Fintype V] [DecidableEq V]
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

lemma in694_private_pair_card_le_one {V : Type*} [DecidableEq V]
    (q : Finset V) (a b y : V) (ha : a ∉ q) (hb : b ∉ q) :
    (({a,b,y} : Finset V) ∩ q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
  aesop

lemma in694_private_free_pair_card_le_one {V : Type*} [DecidableEq V]
    (q : Finset V) (a c x : V) (ha : a ∉ q) (hcx : ¬ (c ∈ q ∧ x ∈ q)) :
    (({a,c,x} : Finset V) ∩ q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv hw
  aesop

lemma in694_private_k4_codegree {V : Type*} [Fintype V] [DecidableEq V]
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
  apply in694_private_swap_impossible G P {a,b,c} {a,b,y} {a,c,x} htri hdisj hmax hp ht hu htu
  · intro q hq hqp
    obtain ⟨ha,hb⟩ := hprivate q hq hqp
    exact in694_private_pair_card_le_one q a b y ha hb
  · intro q hq hqp
    obtain ⟨ha,hb⟩ := hprivate q hq hqp
    exact in694_private_free_pair_card_le_one q a c x ha (hfreecx q hq)


lemma in694_four_distinct {V : Type*} [DecidableEq V] (a b c x : V)
    (h : ({a,b,c,x} : Finset V).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ x ∧ b ≠ c ∧ b ≠ x ∧ c ≠ x := by
  simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
    Finset.card_singleton] at h
  split_ifs at h <;> simp_all

theorem simple_graph_maximum_packing_private_k4_edge_codegree_two (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (a b c x : Fin n) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) (hprivate : ∀ q ∈ P, q ≠ ({a,b,c} : Finset (Fin n)) → a ∉ q ∧ b ∉ q) (hfree : ∀ v ∈ ({a,b,c} : Finset (Fin n)), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) : ∀ y : Fin n, G.Adj a y → G.Adj b y → y = c ∨ y = x := by
  classical
  obtain ⟨hab,hac,hax,hbc,hbx,hcx⟩ := in694_four_distinct a b c x hk4.card_eq
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
  exact in694_private_k4_codegree G P a b c x htri hdisj hmax hp
    (hadj ha hb hab) (hadj ha hc hac) (hadj ha hx hax) (hadj hc hx hcx) hbc hbx hprivate hfreecx
