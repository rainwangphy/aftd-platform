import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_forced_k4_face_pivot_retains_forcing

Topic: graphs   Node: c829841d93ab

Provenance: helper lemma. Local face-pivot obstruction in the internal-anchor forced-K4 branch of the triangle-packing campaign; no novelty claim.

If an edge-disjoint triangle packing contains abc and a four-clique abcx has no packed spokes ax, bx, cx, replacing abc by abx preserves the packing size and produces another fully singleton-forced packed triangle.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open scoped Sym2
namespace In700
lemma in700_encoding_disjoint {V : Type*} [DecidableEq V] (s t : Finset V)
    (h : (s ∩ t).card ≤ 1) :
    Disjoint (finite_vertex_set_edge_encoding s) (finite_vertex_set_edge_encoding t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hes het
  induction e using Sym2.ind with
  | _ u v =>
    simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.isDiag_iff_proj_eq] at hes het
    have hm : u ∈ s ∩ t := Finset.mem_inter.mpr ⟨hes.1.1,het.1.1⟩
    have hn : v ∈ s ∩ t := Finset.mem_inter.mpr ⟨hes.1.2,het.1.2⟩
    have hne : u ≠ v := hes.2
    have hh : 1 < (s ∩ t).card := Finset.one_lt_card.mpr ⟨u,hm,v,hn,hne⟩
    omega

lemma in700_encoding_three {V : Type*} [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    finite_vertex_set_edge_encoding ({a,b,c} : Finset V) = {s(a,b),s(b,c),s(c,a)} := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.mk_isDiag_iff, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    aesop

lemma in700_triangle_witness {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset (Sym2 V)) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htri : G.IsNClique 3 ({a,b,c} : Finset V))
    (h1 : s(a,b) ∈ U) (h2 : s(b,c) ∉ U) (h3 : s(c,a) ∉ U) :
    s(a,b) ∈ (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ U).card = 1)).biUnion id) := by
  classical
  let T := finite_vertex_set_edge_encoding ({a,b,c} : Finset V)
  have henc : T = {s(a,b),s(b,c),s(c,a)} := in700_encoding_three a b c hab hac hbc
  have hcap : T ∩ U = {s(a,b)} := by
    rw [henc]
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hz⟩
      · rfl
      · exact (h2 hz).elim
      · exact (h3 hz).elim
    · rintro rfl
      exact ⟨Or.inl rfl,h1⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨T, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · unfold simple_graph_triangle_edge_family
    apply Finset.mem_image.mpr
    exact ⟨{a,b,c}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htri⟩, rfl⟩
  · simp [hcap]
  · simp [henc]

lemma in700_four_edges_subset {V : Type*} [DecidableEq V] (a b c x : V) :
    finite_vertex_set_edge_encoding ({a,b,c,x} : Finset V) ⊆
      finite_vertex_set_edge_encoding ({a,b,c} : Finset V) ∪ {s(a,x),s(b,x),s(c,x)} := by
  classical
  intro z hz
  induction z using Sym2.ind with
  | _ u v =>
    simp only [finite_vertex_set_edge_encoding, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.mk_isDiag_iff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
      Sym2.eq_iff] at hz ⊢
    aesop

lemma in700_old_edges_disjoint_four {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V)) (a b c x : V)
    (hdisj : (P : Set (Finset V)).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hp : ({a,b,c} : Finset V) ∈ P)
    (hfree : ∀ e ∈ ({s(a,x),s(b,x),s(c,x)} : Finset (Sym2 V)),
      e ∉ P.biUnion finite_vertex_set_edge_encoding) :
    Disjoint (finite_vertex_set_edge_encoding ({a,b,c,x} : Finset V))
      ((P.erase {a,b,c}).biUnion finite_vertex_set_edge_encoding) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hU
  obtain ⟨q,hq,hzq⟩ := Finset.mem_biUnion.mp hU
  obtain ⟨hneq,hqP⟩ := Finset.mem_erase.mp hq
  have hor := in700_four_edges_subset a b c x hz
  rcases Finset.mem_union.mp hor with hzold | hzspoke
  · have hd := in700_encoding_disjoint q {a,b,c} (hdisj hqP hp hneq)
    exact Finset.disjoint_left.mp hd hzq hzold
  · apply hfree z hzspoke
    exact Finset.mem_biUnion.mpr ⟨q,hqP,hzq⟩

lemma in700_four_distinct {V : Type*} [DecidableEq V] {a b c x : V}
    (h : ({a,b,c,x} : Finset V).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ x ∧ b ≠ c ∧ b ≠ x ∧ c ≠ x := by
  have le3 (u v w : V) : ({u,v,w} : Finset V).card ≤ 3 := by
    have h1 := Finset.card_insert_le u ({v,w} : Finset V)
    have h2 := Finset.card_insert_le v ({w} : Finset V)
    simp only [Finset.card_singleton] at *
    omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rintro rfl
    have he : ({a,a,c,x} : Finset V) = {a,c,x} := by ext z; simp <;> tauto
    rw [he] at h; have := le3 a c x; omega
  · rintro rfl
    have he : ({a,b,a,x} : Finset V) = {a,b,x} := by ext z; simp <;> tauto
    rw [he] at h; have := le3 a b x; omega
  · rintro rfl
    have he : ({a,b,c,a} : Finset V) = {a,b,c} := by ext z; simp <;> tauto
    rw [he] at h; have := le3 a b c; omega
  · rintro rfl
    have he : ({a,b,b,x} : Finset V) = {a,b,x} := by ext z; simp <;> tauto
    rw [he] at h; have := le3 a b x; omega
  · rintro rfl
    have he : ({a,b,c,b} : Finset V) = {a,b,c} := by ext z; simp <;> tauto
    rw [he] at h; have := le3 a b c; omega
  · rintro rfl
    have he : ({a,b,c,c} : Finset V) = {a,b,c} := by ext z; simp <;> tauto
    rw [he] at h; have := le3 a b c; omega

lemma in700_encoding_disjoint_iff {V : Type*} [DecidableEq V] (s t : Finset V)
    (h : Disjoint (finite_vertex_set_edge_encoding s) (finite_vertex_set_edge_encoding t)) :
    (s ∩ t).card ≤ 1 := by
  classical
  by_contra hn
  have hh : 1 < (s ∩ t).card := by omega
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hh
  obtain ⟨hus,hut⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvs,hvt⟩ := Finset.mem_inter.mp hv
  have h1 : s(u,v) ∈ finite_vertex_set_edge_encoding s := by
    simp [finite_vertex_set_edge_encoding, hus, hvs, huv]
  have h2 : s(u,v) ∈ finite_vertex_set_edge_encoding t := by
    simp [finite_vertex_set_edge_encoding, hut, hvt, huv]
  exact Finset.disjoint_left.mp h h1 h2

lemma in700_encoding_mono {V : Type*} [DecidableEq V] {s t : Finset V}
    (h : s ⊆ t) : finite_vertex_set_edge_encoding s ⊆ finite_vertex_set_edge_encoding t := by
  intro z hz
  obtain ⟨hm,hd⟩ := Finset.mem_filter.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨?_,hd⟩
  rw [Finset.mem_sym2_iff] at hm ⊢
  exact fun a ha => h (hm a ha)

lemma in700_card_three {V : Type*} [DecidableEq V] {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a,b,c} : Finset V).card = 3 := by
  have hc : ({c} : Finset V).card = 1 := Finset.card_singleton c
  have hbc' : b ∉ ({c} : Finset V) := by simp [hbc]
  have hb : ({b,c} : Finset V).card = 2 := by rw [Finset.card_insert_of_notMem hbc',hc]
  have ha : a ∉ ({b,c} : Finset V) := by simp [hab,hac]
  rw [Finset.card_insert_of_notMem ha,hb]

lemma in700_clique_subset {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (K t : Finset V) (hK : G.IsNClique 4 K) (hsub : t ⊆ K) (hcard : t.card = 3) :
    G.IsNClique 3 t := by
  refine ⟨?_,hcard⟩
  intro u hu v hv hne
  exact hK.1 (hsub hu) (hsub hv) hne

theorem in700_main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Finset (Fin n))) (a b c x : Fin n)
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hp : ({a,b,c} : Finset (Fin n)) ∈ P)
    (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n)))
    (hfree : ∀ e ∈ ({s(a,x),s(b,x),s(c,x)} : Finset (Sym2 (Fin n))),
      e ∉ P.biUnion finite_vertex_set_edge_encoding) :
    let Q := insert ({a,b,x} : Finset (Fin n)) (P.erase {a,b,c});
    Q.card = P.card ∧ (∀ t ∈ Q, G.IsNClique 3 t) ∧
    (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) ∧
    finite_vertex_set_edge_encoding ({a,b,x} : Finset (Fin n)) ⊆
      (((simple_graph_triangle_edge_family G).filter
        (fun t => (t ∩ Q.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) := by
  classical
  obtain ⟨hab,hac,hax,hbc,hbx,hcx⟩ := in700_four_distinct hk4.card_eq
  let K : Finset (Fin n) := {a,b,c,x}
  let T : Finset (Fin n) := {a,b,x}
  let R := P.erase ({a,b,c} : Finset (Fin n))
  let Q := insert T R
  change Q.card = P.card ∧ (∀ t ∈ Q, G.IsNClique 3 t) ∧
    (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) ∧
    finite_vertex_set_edge_encoding T ⊆
      (((simple_graph_triangle_edge_family G).filter
        (fun t => (t ∩ Q.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)
  have hsub : T ⊆ K := by simp [T,K,Finset.subset_iff] <;> tauto
  have hK := in700_old_edges_disjoint_four P a b c x hdisj hp hfree
  change Disjoint (finite_vertex_set_edge_encoding K) (R.biUnion finite_vertex_set_edge_encoding) at hK
  have hT : Disjoint (finite_vertex_set_edge_encoding T) (R.biUnion finite_vertex_set_edge_encoding) :=
    hK.mono_left (in700_encoding_mono hsub)
  have haxT : s(a,x) ∈ finite_vertex_set_edge_encoding T := by
    simp [T,finite_vertex_set_edge_encoding,hax]
  have hTnot : T ∉ R := by
    intro hm
    apply Finset.disjoint_left.mp hT haxT
    exact Finset.mem_biUnion.mpr ⟨T,hm,haxT⟩
  have hTcl : G.IsNClique 3 T := by
    apply in700_clique_subset G K T hk4 hsub
    exact in700_card_three hab hax hbx
  have hcard : Q.card = P.card := by
    change (insert T R).card = P.card
    rw [Finset.card_insert_of_notMem hTnot]
    dsimp [R]
    rw [Finset.card_erase_of_mem hp]
    have : 0 < P.card := Finset.card_pos.mpr ⟨{a,b,c},hp⟩
    omega
  have hpair : (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) := by
    intro t ht u hu hne
    simp only [Q,Finset.mem_coe,Finset.mem_insert] at ht hu
    rcases ht with rfl | ht <;> rcases hu with rfl | hu
    · exact (hne rfl).elim
    · apply in700_encoding_disjoint_iff
      apply Finset.disjoint_left.mpr
      intro z hzT hzu
      exact Finset.disjoint_left.mp hT hzT (Finset.mem_biUnion.mpr ⟨u,hu,hzu⟩)
    · apply in700_encoding_disjoint_iff
      apply Finset.disjoint_left.mpr
      intro z hzt hzT
      exact Finset.disjoint_left.mp hT hzT (Finset.mem_biUnion.mpr ⟨t,ht,hzt⟩)
    · exact hdisj (Finset.mem_of_mem_erase ht) (Finset.mem_of_mem_erase hu) hne
  have hblock : ∀ w ∈ K, w ≠ c → s(c,w) ∉ Q.biUnion finite_vertex_set_edge_encoding := by
    intro w hw hwc
    have hw' : w = a ∨ w = b ∨ w = x := by simpa [K,hwc] using hw
    have heK : s(c,w) ∈ finite_vertex_set_edge_encoding K := by
      simp [finite_vertex_set_edge_encoding,K,hw',hwc,Ne.symm hwc]
    have heT : s(c,w) ∉ finite_vertex_set_edge_encoding T := by
      simp [finite_vertex_set_edge_encoding,T,Ne.symm hac,Ne.symm hbc,hcx]
    intro hm
    obtain ⟨q,hq,hzq⟩ := Finset.mem_biUnion.mp hm
    simp only [Q,Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact heT hzq
    · exact Finset.disjoint_left.mp hK heK (Finset.mem_biUnion.mpr ⟨q,hq,hzq⟩)
  have hca : s(c,a) ∉ Q.biUnion finite_vertex_set_edge_encoding :=
    hblock a (by simp [K]) hac
  have hcb : s(c,b) ∉ Q.biUnion finite_vertex_set_edge_encoding :=
    hblock b (by simp [K]) hbc
  have hcx' : s(c,x) ∉ Q.biUnion finite_vertex_set_edge_encoding :=
    hblock x (by simp [K]) (Ne.symm hcx)
  have hxc : s(x,c) ∉ Q.biUnion finite_vertex_set_edge_encoding := by
    rw [Sym2.eq_swap]; exact hcx'
  have hbc' : s(b,c) ∉ Q.biUnion finite_vertex_set_edge_encoding := by
    rw [Sym2.eq_swap]; exact hcb
  have hac' : s(a,c) ∉ Q.biUnion finite_vertex_set_edge_encoding := by
    rw [Sym2.eq_swap]; exact hca
  have habU : s(a,b) ∈ Q.biUnion finite_vertex_set_edge_encoding := by
    apply Finset.mem_biUnion.mpr
    exact ⟨T,Finset.mem_insert_self T R,by simp [T,finite_vertex_set_edge_encoding,hab]⟩
  have hbxU : s(b,x) ∈ Q.biUnion finite_vertex_set_edge_encoding := by
    apply Finset.mem_biUnion.mpr
    exact ⟨T,Finset.mem_insert_self T R,by simp [T,finite_vertex_set_edge_encoding,hbx]⟩
  have hxaU : s(x,a) ∈ Q.biUnion finite_vertex_set_edge_encoding := by
    apply Finset.mem_biUnion.mpr
    exact ⟨T,Finset.mem_insert_self T R,by simp [T,finite_vertex_set_edge_encoding,Ne.symm hax]⟩
  have hxca : G.IsNClique 3 ({x,a,c} : Finset (Fin n)) := by
    apply in700_clique_subset G K _ hk4
    · simp [K,Finset.subset_iff] <;> tauto
    · exact in700_card_three (Ne.symm hax) (Ne.symm hcx) hac
  have hbxc : G.IsNClique 3 ({b,x,c} : Finset (Fin n)) := by
    apply in700_clique_subset G K _ hk4
    · simp [K,Finset.subset_iff] <;> tauto
    · exact in700_card_three hbx hbc (Ne.symm hcx)
  refine ⟨hcard, ?_, hpair, ?_⟩
  · intro t ht
    simp only [Q,Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact hTcl
    · exact htri t (Finset.mem_of_mem_erase ht)
  · intro z hz
    rw [in700_encoding_three a b x hab hax hbx] at hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact in700_triangle_witness G _ a b c hab hac hbc (htri _ hp) habU hbc' hca
    · exact in700_triangle_witness G _ b x c hbx hbc (Ne.symm hcx) hbxc hbxU hxc hcb
    · exact in700_triangle_witness G _ x a c (Ne.symm hax) (Ne.symm hcx) hac hxca hxaU hac' hcx'
end In700

theorem simple_graph_forced_k4_face_pivot_retains_forcing (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (a b c x : Fin n) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) (hfree : ∀ e ∈ ({s(a,x),s(b,x),s(c,x)} : Finset (Sym2 (Fin n))), e ∉ P.biUnion finite_vertex_set_edge_encoding) : let Q := insert ({a,b,x} : Finset (Fin n)) (P.erase {a,b,c}); Q.card = P.card ∧ (∀ t ∈ Q, G.IsNClique 3 t) ∧ (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) ∧ finite_vertex_set_edge_encoding ({a,b,x} : Finset (Fin n)) ⊆ (((simple_graph_triangle_edge_family G).filter (fun t => (t ∩ Q.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) := by
  exact In700.in700_main n G P a b c x htri hdisj hp hk4 hfree
