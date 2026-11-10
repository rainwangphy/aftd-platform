import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.FiniteMaximumPackingPrivateWitnessesIntersect
import AFTD.Kb.Tcs.FiniteVertexFamilyEdgePackingCoverBridge
import AFTD.Kb.Tcs.SimpleGraphForcedK4FacePivotRetainsForcing

/-!
# simple_graph_maximum_packing_two_forced_edges_k4

Topic: graphs   Node: d7cfe6d10bc4

Provenance: helper lemma. Local private-witness K4 structure in https://arxiv.org/abs/2001.00257, Section 3; the two-forced-edge formulation is used as a bridge for the triangle-packing campaign.

For a maximum triangle packing, if a packed triangle has two singleton-forced edges then its three vertices have a common fourth vertex forming a four-clique, none of the three new spokes is a packing edge, and all three packed edges are singleton-forced. Hence a packed triangle has 0, 1, or 3 singleton-forced edges, never exactly 2.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped Sym2
namespace In701

lemma family_max {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V))
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset V)).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G) :
    ∀ Q : Finset (Finset (Sym2 V)), Q ⊆ simple_graph_triangle_edge_family G →
      (Q : Set (Finset (Sym2 V))).Pairwise Disjoint →
      Q.card ≤ (P.image finite_vertex_set_edge_encoding).card := by
  classical
  intro Q hQ hQdis
  let Tall : Finset (Finset V) := Finset.univ.filter (G.IsNClique 3)
  let R : Finset (Finset V) := Tall.filter (fun t => finite_vertex_set_edge_encoding t ∈ Q)
  have hRtri : ∀ t ∈ R, G.IsNClique 3 t := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
  have hRsize : ∀ t ∈ R, 2 ≤ t.card := by
    intro t ht
    have h := (hRtri t ht).card_eq
    omega
  have himage : R.image finite_vertex_set_edge_encoding = Q := by
    ext e
    constructor
    · intro he
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp ht).2
    · intro he
      have he' := hQ he
      change e ∈ Tall.image finite_vertex_set_edge_encoding at he'
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp he'
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,he⟩,rfl⟩
  have hRbridge := finite_vertex_family_edge_packing_cover_bridge R (∅ : Finset (Sym2 V)) hRsize (by simp)
  have hRdis : (R : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) := by
    apply hRbridge.2.1.mp
    simpa [himage] using hQdis
  have hRcard : Q.card = R.card := by rw [← himage]; exact hRbridge.1
  have hRbound : R.card ≤ simple_graph_triangle_packing_number G := by
    unfold simple_graph_triangle_packing_number
    apply le_csSup
    · refine ⟨Fintype.card (Finset V), ?_⟩
      rintro k ⟨T,_,_,rfl⟩
      exact Finset.card_le_univ T
    · exact ⟨R,hRtri,hRdis,rfl⟩
  have hPsize : ∀ t ∈ P, 2 ≤ t.card := by
    intro t ht
    have h := (htri t ht).card_eq
    omega
  have hPbridge := finite_vertex_family_edge_packing_cover_bridge P (∅ : Finset (Sym2 V)) hPsize (by simp)
  rw [hPbridge.1,hRcard,hmax]
  exact hRbound

lemma witnesses_meet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V))
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset V)).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (p : Finset V) (hp : p ∈ P) (T U : Finset (Sym2 V))
    (hT : T ∈ simple_graph_triangle_edge_family G)
    (hU : U ∈ simple_graph_triangle_edge_family G)
    (hTp : ∀ e ∈ T, e ∈ P.biUnion finite_vertex_set_edge_encoding → e ∈ finite_vertex_set_edge_encoding p)
    (hUp : ∀ e ∈ U, e ∈ P.biUnion finite_vertex_set_edge_encoding → e ∈ finite_vertex_set_edge_encoding p) :
    ¬ Disjoint T U := by
  classical
  let F := simple_graph_triangle_edge_family G
  let Q := P.image finite_vertex_set_edge_encoding
  have hnonempty : ∀ t ∈ F, t.Nonempty := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    have hscl : G.IsNClique 3 s := (Finset.mem_filter.mp hs).2
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hscl.card_eq
    refine ⟨s(a,b), ?_⟩
    simp [finite_vertex_set_edge_encoding, hab]
  have hQF : Q ⊆ F := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,htri s hs⟩,rfl⟩
  have hPsize : ∀ t ∈ P, 2 ≤ t.card := by
    intro t ht
    have h := (htri t ht).card_eq
    omega
  have hQdis : (Q : Set (Finset (Sym2 V))).Pairwise Disjoint :=
    (finite_vertex_family_edge_packing_cover_bridge P (∅ : Finset (Sym2 V)) hPsize (by simp)).2.1.mpr hdisj
  have hQmax : ∀ R : Finset (Finset (Sym2 V)), R ⊆ F →
      (R : Set (Finset (Sym2 V))).Pairwise Disjoint → R.card ≤ Q.card :=
    family_max G P htri hdisj hmax
  have hprivate (T : Finset (Sym2 V))
      (htp : ∀ e ∈ T, e ∈ P.biUnion finite_vertex_set_edge_encoding → e ∈ finite_vertex_set_edge_encoding p) :
      ∀ q ∈ Q, q ≠ finite_vertex_set_edge_encoding p → Disjoint q T := by
    intro q hq hne
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    apply Finset.disjoint_left.mpr
    intro e her heT
    have heU : e ∈ P.biUnion finite_vertex_set_edge_encoding := Finset.mem_biUnion.mpr ⟨r,hr,her⟩
    have hep := htp e heT heU
    exact Finset.disjoint_left.mp (hQdis (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
      (Finset.mem_image.mpr ⟨p,hp,rfl⟩) hne) her hep
  exact finite_maximum_packing_private_witnesses_intersect F Q hnonempty hQF hQdis hQmax
    (finite_vertex_set_edge_encoding p) T U hT hU (hprivate T hTp) (hprivate U hUp)

end In701

namespace In701
lemma triangle_third {V : Type*} [DecidableEq V] (T : Finset V) (a b : V)
    (hT : T.card = 3) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ T = {a,b,x} := by
  obtain ⟨u,v,w,huv,huw,hvw,rfl⟩ := Finset.card_eq_three.mp hT
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals simp_all
  all_goals first | exact ⟨u, by aesop, by aesop, by ext z; simp <;> tauto⟩ | exact ⟨v, by aesop, by aesop, by ext z; simp <;> tauto⟩ | exact ⟨w, by aesop, by aesop, by ext z; simp <;> tauto⟩

lemma witness_at_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) (e : Sym2 V)
    (hePacked : e ∈ P.biUnion finite_vertex_set_edge_encoding)
    (he : e ∈ (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)) :
    ∃ T : Finset V, G.IsNClique 3 T ∧ e ∈ finite_vertex_set_edge_encoding T ∧
      finite_vertex_set_edge_encoding T ∩ P.biUnion finite_vertex_set_edge_encoding = {e} := by
  classical
  obtain ⟨F,hF,heF⟩ := Finset.mem_biUnion.mp he
  obtain ⟨hFG,hFcard⟩ := Finset.mem_filter.mp hF
  obtain ⟨T,hTG,rfl⟩ := Finset.mem_image.mp hFG
  have hT : G.IsNClique 3 T := (Finset.mem_filter.mp hTG).2
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hFcard
  have hez : e = z := by
    have : e ∈ finite_vertex_set_edge_encoding T ∩ P.biUnion finite_vertex_set_edge_encoding := Finset.mem_inter.mpr ⟨heF,hePacked⟩
    simpa [hz] using this
  subst z
  exact ⟨T,hT,heF,hz⟩
end In701

namespace In701
lemma two_edges_ordered {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V))
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset V)).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : ({a,b,c} : Finset V) ∈ P)
    (hAB : s(a,b) ∈ (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id))
    (hAC : s(a,c) ∈ (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)) :
    ∃ x, x ∉ ({a,b,c} : Finset V) ∧ G.IsNClique 4 ({a,b,c,x} : Finset V) ∧
      (∀ v ∈ ({a,b,c} : Finset V), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) := by
  classical
  let W := P.biUnion finite_vertex_set_edge_encoding
  have hPacked (e : Sym2 V) (he : e ∈ finite_vertex_set_edge_encoding ({a,b,c} : Finset V)) : e ∈ W :=
    Finset.mem_biUnion.mpr ⟨{a,b,c},hp,he⟩
  have habP : s(a,b) ∈ W := hPacked _ (by simp [finite_vertex_set_edge_encoding,hab])
  have hacP : s(a,c) ∈ W := hPacked _ (by simp [finite_vertex_set_edge_encoding,hac])
  have hbcP : s(b,c) ∈ W := hPacked _ (by simp [finite_vertex_set_edge_encoding,hbc])
  obtain ⟨T,hTG,heT,hTcap⟩ := witness_at_edge G P s(a,b) habP hAB
  obtain ⟨U,hUG,heU,hUcap⟩ := witness_at_edge G P s(a,c) hacP hAC
  have hmT : a ∈ T ∧ b ∈ T := by
    simpa [finite_vertex_set_edge_encoding,hab] using heT
  have hmU : a ∈ U ∧ c ∈ U := by
    simpa [finite_vertex_set_edge_encoding,hac] using heU
  obtain ⟨x,hxa,hxb,hT⟩ := triangle_third T a b hTG.card_eq hmT.1 hmT.2 hab
  obtain ⟨y,hya,hyc,hU⟩ := triangle_third U a c hUG.card_eq hmU.1 hmU.2 hac
  subst T
  subst U
  have hxc : x ≠ c := by
    intro h; subst x
    have hx : s(a,c) ∈ finite_vertex_set_edge_encoding ({a,b,c} : Finset V) ∩ W :=
      Finset.mem_inter.mpr ⟨by simp [finite_vertex_set_edge_encoding,hac],hacP⟩
    rw [hTcap] at hx
    simp only [Finset.mem_singleton, Sym2.eq_iff] at hx
    aesop
  have hyb : y ≠ b := by
    intro h; subst y
    have hx : s(a,b) ∈ finite_vertex_set_edge_encoding ({a,c,b} : Finset V) ∩ W :=
      Finset.mem_inter.mpr ⟨by simp [finite_vertex_set_edge_encoding,hab],habP⟩
    rw [hUcap] at hx
    simp only [Finset.mem_singleton, Sym2.eq_iff] at hx
    aesop
  have hTp : ∀ e ∈ finite_vertex_set_edge_encoding ({a,b,x} : Finset V), e ∈ W → e ∈ finite_vertex_set_edge_encoding ({a,b,c} : Finset V) := by
    intro e he heW
    have hh : e ∈ ({s(a,b)} : Finset (Sym2 V)) := by rw [← hTcap]; exact Finset.mem_inter.mpr ⟨he,heW⟩
    have : e = s(a,b) := Finset.mem_singleton.mp hh
    subst e
    simp [finite_vertex_set_edge_encoding,hab]
  have hUp : ∀ e ∈ finite_vertex_set_edge_encoding ({a,c,y} : Finset V), e ∈ W → e ∈ finite_vertex_set_edge_encoding ({a,b,c} : Finset V) := by
    intro e he heW
    have hh : e ∈ ({s(a,c)} : Finset (Sym2 V)) := by rw [← hUcap]; exact Finset.mem_inter.mpr ⟨he,heW⟩
    have : e = s(a,c) := Finset.mem_singleton.mp hh
    subst e
    simp [finite_vertex_set_edge_encoding,hac]
  have hTF : finite_vertex_set_edge_encoding ({a,b,x} : Finset V) ∈ simple_graph_triangle_edge_family G := by
    exact Finset.mem_image.mpr ⟨{a,b,x},Finset.mem_filter.mpr ⟨Finset.mem_univ _,hTG⟩,rfl⟩
  have hUF : finite_vertex_set_edge_encoding ({a,c,y} : Finset V) ∈ simple_graph_triangle_edge_family G := by
    exact Finset.mem_image.mpr ⟨{a,c,y},Finset.mem_filter.mpr ⟨Finset.mem_univ _,hUG⟩,rfl⟩
  have hmeet := witnesses_meet G P htri hdisj hmax {a,b,c} hp _ _ hTF hUF hTp hUp
  have hxy : x = y := by
    by_contra hxy
    apply hmeet
    rw [In700.in700_encoding_three a b x hab (Ne.symm hxa) (Ne.symm hxb),
      In700.in700_encoding_three a c y hac (Ne.symm hya) (Ne.symm hyc)]
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    aesop
  subst y
  have hfreeAX : s(a,x) ∉ W := by
    intro he
    have hh : s(a,x) ∈ ({s(a,b)} : Finset (Sym2 V)) := by rw [← hTcap]; exact Finset.mem_inter.mpr ⟨by simp [finite_vertex_set_edge_encoding,Ne.symm hxa],he⟩
    simp only [Finset.mem_singleton,Sym2.eq_iff] at hh
    aesop
  have hfreeBX : s(b,x) ∉ W := by
    intro he
    have hh : s(b,x) ∈ ({s(a,b)} : Finset (Sym2 V)) := by rw [← hTcap]; exact Finset.mem_inter.mpr ⟨by simp [finite_vertex_set_edge_encoding,Ne.symm hxb],he⟩
    simp only [Finset.mem_singleton,Sym2.eq_iff] at hh
    aesop
  have hfreeCX : s(c,x) ∉ W := by
    intro he
    have hh : s(c,x) ∈ ({s(a,c)} : Finset (Sym2 V)) := by rw [← hUcap]; exact Finset.mem_inter.mpr ⟨by simp [finite_vertex_set_edge_encoding,Ne.symm hxc],he⟩
    simp only [Finset.mem_singleton,Sym2.eq_iff] at hh
    aesop
  refine ⟨x,by simp [hxa,hxb,hxc],?_,?_⟩
  · constructor
    · have habG : G.Adj a b := (htri _ hp).1 (by simp) (by simp) hab
      have hacG : G.Adj a c := (htri _ hp).1 (by simp) (by simp) hac
      have hbcG : G.Adj b c := (htri _ hp).1 (by simp) (by simp) hbc
      have haxG : G.Adj a x := hTG.1 (by simp) (by simp) (Ne.symm hxa)
      have hbxG : G.Adj b x := hTG.1 (by simp) (by simp) (Ne.symm hxb)
      have hcxG : G.Adj c x := hUG.1 (by simp) (by simp) (Ne.symm hxc)
      intro u hu v hv huv
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
      all_goals first | contradiction | assumption | exact SimpleGraph.Adj.symm (by assumption)
    · have heq : ({a,b,c,x} : Finset V) = insert x {a,b,c} := by
        ext z
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto
      rw [heq,Finset.card_insert_of_notMem (by simp [hxa,hxb,hxc]), In700.in700_card_three hab hac hbc]
  · intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · simpa only [Sym2.eq_swap] using hfreeAX
    · simpa only [Sym2.eq_swap] using hfreeBX
    · simpa only [Sym2.eq_swap] using hfreeCX
end In701

namespace In701
lemma k4_all_forced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V))
    (a b c x : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : ({a,b,c} : Finset V) ∈ P)
    (hx : x ∉ ({a,b,c} : Finset V))
    (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset V))
    (hfree : ∀ v ∈ ({a,b,c} : Finset V), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) :
    finite_vertex_set_edge_encoding ({a,b,c} : Finset V) ⊆
      (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) := by
  classical
  have hxa : x ≠ a := by intro h; subst x; exact hx (by simp)
  have hxb : x ≠ b := by intro h; subst x; exact hx (by simp)
  have hxc : x ≠ c := by intro h; subst x; exact hx (by simp)
  let W := P.biUnion finite_vertex_set_edge_encoding
  have hPacked (e : Sym2 V) (he : e ∈ finite_vertex_set_edge_encoding ({a,b,c} : Finset V)) : e ∈ W :=
    Finset.mem_biUnion.mpr ⟨{a,b,c},hp,he⟩
  have hfa : s(a,x) ∉ W := by simpa only [Sym2.eq_swap] using hfree a (by simp)
  have hfb : s(b,x) ∉ W := by simpa only [Sym2.eq_swap] using hfree b (by simp)
  have hfc : s(c,x) ∉ W := by simpa only [Sym2.eq_swap] using hfree c (by simp)
  have ht (u v : V) (hu : u ∈ ({a,b,c} : Finset V)) (hv : v ∈ ({a,b,c} : Finset V))
      (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x) : G.IsNClique 3 ({u,v,x} : Finset V) := by
    apply In700.in700_clique_subset G {a,b,c,x} {u,v,x} hk4
    · intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
      aesop
    · exact In700.in700_card_three huv hux hvx
  have hab' := In700.in700_triangle_witness G W a b x hab (Ne.symm hxa) (Ne.symm hxb)
    (ht a b (by simp) (by simp) hab (Ne.symm hxa) (Ne.symm hxb))
    (hPacked _ (by simp [finite_vertex_set_edge_encoding,hab])) hfb (by simpa only [Sym2.eq_swap] using hfa)
  have hbc' := In700.in700_triangle_witness G W b c x hbc (Ne.symm hxb) (Ne.symm hxc)
    (ht b c (by simp) (by simp) hbc (Ne.symm hxb) (Ne.symm hxc))
    (hPacked _ (by simp [finite_vertex_set_edge_encoding,hbc])) hfc (by simpa only [Sym2.eq_swap] using hfb)
  have hca' := In700.in700_triangle_witness G W c a x (Ne.symm hac) (Ne.symm hxc) (Ne.symm hxa)
    (ht c a (by simp) (by simp) (Ne.symm hac) (Ne.symm hxc) (Ne.symm hxa))
    (hPacked _ (by simp [finite_vertex_set_edge_encoding,Ne.symm hac])) hfa (by simpa only [Sym2.eq_swap] using hfc)
  rw [In700.in700_encoding_three a b c hab hac hbc]
  intro e he
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> assumption
end In701

open In701

lemma in701_choose {V : Type*} [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (F : Finset (Sym2 V))
    (hmarked : 2 ≤ (finite_vertex_set_edge_encoding ({a,b,c} : Finset V) ∩ F).card) :
    (s(a,b) ∈ F ∧ s(a,c) ∈ F) ∨ (s(b,a) ∈ F ∧ s(b,c) ∈ F) ∨
    (s(c,a) ∈ F ∧ s(c,b) ∈ F) := by
  have hmany : 1 < (finite_vertex_set_edge_encoding ({a,b,c} : Finset V) ∩ F).card := by omega
  obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hmany
  have heF : e ∈ F := (Finset.mem_inter.mp he).2
  have hfF : f ∈ F := (Finset.mem_inter.mp hf).2
  have heE := (Finset.mem_inter.mp he).1
  have hfE := (Finset.mem_inter.mp hf).1
  rw [In700.in700_encoding_three a b c hab hac hbc] at heE hfE
  simp only [Finset.mem_insert,Finset.mem_singleton] at heE hfE
  rcases heE with heE | heE | heE
  · subst e
    rcases hfE with hfE | hfE | hfE
    · subst f; exact (hef rfl).elim
    · subst f; right; left; exact ⟨by simpa only [Sym2.eq_swap] using heF,hfF⟩
    · subst f; left; exact ⟨heF,by simpa only [Sym2.eq_swap] using hfF⟩
  · subst e
    rcases hfE with hfE | hfE | hfE
    · subst f; right; left; exact ⟨by simpa only [Sym2.eq_swap] using hfF,heF⟩
    · subst f; exact (hef rfl).elim
    · subst f; right; right; exact ⟨hfF, by simpa only [Sym2.eq_swap] using heF⟩
  · subst e
    rcases hfE with hfE | hfE | hfE
    · subst f; left; exact ⟨hfF,by simpa only [Sym2.eq_swap] using heF⟩
    · subst f; right; right; exact ⟨heF,by simpa only [Sym2.eq_swap] using hfF⟩
    · subst f; exact (hef rfl).elim

lemma in701_k4_choose (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Finset (Fin n)))
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : ({a,b,c} : Finset (Fin n)) ∈ P)
    (hchoose : let F := (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)
      (s(a,b) ∈ F ∧ s(a,c) ∈ F) ∨ (s(b,a) ∈ F ∧ s(b,c) ∈ F) ∨
      (s(c,a) ∈ F ∧ s(c,b) ∈ F)) :
    ∃ x, x ∉ ({a,b,c} : Finset (Fin n)) ∧ G.IsNClique 4 ({a,b,c,x} : Finset (Fin n)) ∧
      (∀ v ∈ ({a,b,c} : Finset (Fin n)), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) := by
  classical
    rcases hchoose with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact two_edges_ordered G P htri hdisj hmax a b c hab hac hbc hp h1 h2
    · have hperm : ({b,a,c} : Finset (Fin n)) = {a,b,c} := by ext z; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      have hperm4 (x : Fin n) : ({b,a,c,x} : Finset (Fin n)) = {a,b,c,x} := by ext z; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      have hp' : ({b,a,c} : Finset (Fin n)) ∈ P := by simpa only [hperm] using hp
      obtain ⟨x,hx,hfour,hfree⟩ := two_edges_ordered G P htri hdisj hmax b a c (Ne.symm hab) hbc hac hp' h1 h2
      exact ⟨x,by simpa only [hperm] using hx,by simpa only [hperm4] using hfour,by simpa only [hperm] using hfree⟩
    · have hperm : ({c,a,b} : Finset (Fin n)) = {a,b,c} := by ext z; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      have hperm4 (x : Fin n) : ({c,a,b,x} : Finset (Fin n)) = {a,b,c,x} := by ext z; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      have hp' : ({c,a,b} : Finset (Fin n)) ∈ P := by simpa only [hperm] using hp
      obtain ⟨x,hx,hfour,hfree⟩ := two_edges_ordered G P htri hdisj hmax c a b (Ne.symm hac) (Ne.symm hbc) hab hp' h1 h2
      exact ⟨x,by simpa only [hperm] using hx,by simpa only [hperm4] using hfour,by simpa only [hperm] using hfree⟩

lemma in701_insert_four {V : Type*} [DecidableEq V] (a b c x : V) :
    insert x ({a,b,c} : Finset V) = {a,b,c,x} := by
  ext z
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

lemma in701_main_ordered (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Finset (Fin n)))
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : ({a,b,c} : Finset (Fin n)) ∈ P)
    (hmarked : 2 ≤ (finite_vertex_set_edge_encoding ({a,b,c} : Finset (Fin n)) ∩
      (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)).card) :
    ∃ x : Fin n, x ∉ ({a,b,c} : Finset (Fin n)) ∧ G.IsNClique 4 (insert x {a,b,c}) ∧
      (∀ v ∈ ({a,b,c} : Finset (Fin n)), s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) ∧
      finite_vertex_set_edge_encoding ({a,b,c} : Finset (Fin n)) ⊆ (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) := by
  classical
  let F := (((simple_graph_triangle_edge_family G).filter
      (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)
  have hmarked' : 2 ≤ (finite_vertex_set_edge_encoding ({a,b,c} : Finset (Fin n)) ∩ F).card := hmarked
  have hchoose := in701_choose a b c hab hac hbc F hmarked'
  have hK := in701_k4_choose n G P htri hdisj hmax a b c hab hac hbc hp hchoose
  obtain ⟨x,hx,hfour,hfree⟩ := hK
  refine ⟨x,hx,?_,hfree,k4_all_forced G P a b c x hab hac hbc hp hx hfour hfree⟩
  rw [in701_insert_four]
  exact hfour

theorem simple_graph_maximum_packing_two_forced_edges_k4 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (p : Finset (Fin n)) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hp : p ∈ P) (hmarked : 2 ≤ (finite_vertex_set_edge_encoding p ∩ (((simple_graph_triangle_edge_family G).filter (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)).card) : ∃ x : Fin n, x ∉ p ∧ G.IsNClique 4 (insert x p) ∧ (∀ v ∈ p, s(x,v) ∉ P.biUnion finite_vertex_set_edge_encoding) ∧ finite_vertex_set_edge_encoding p ⊆ (((simple_graph_triangle_edge_family G).filter (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hpEq⟩ := Finset.card_eq_three.mp (htri p hp).card_eq
  subst p
  exact in701_main_ordered n G P htri hdisj hmax a b c hab hac hbc hp hmarked
