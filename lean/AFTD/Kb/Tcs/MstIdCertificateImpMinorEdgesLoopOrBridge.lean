import AFTD.Prelude
import AFTD.Kb.Tcs.MinorEdgeIsLoop
import AFTD.Kb.Tcs.MinorEdgeIsBridge
import AFTD.Kb.Optimization.IsMstCertificate
import AFTD.Kb.Optimization.IsMstFor
import AFTD.Kb.Tcs.IsTreeIffIsAcyclicAndCard
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.G

/-!
# mst_id_certificate_imp_minor_edges_loop_or_bridge

Topic: graphs   Node: ca40d74ba681

Provenance: formalization of a published result. Source: arXiv:2610.40844 Lemma 2.2

If a partial realization β is an MST identification certificate for a connected simple graph G on a finite vertex set, then every unqueried edge of G is either a loop or a bridge in the minor G_β.
-/

open scoped Classical

private noncomputable def mstid_cost {V : Type*} [Fintype V]
    (G : SimpleGraph V) (α : G.edgeSet → Bool) (S : SimpleGraph V) : ℕ :=
  ∑ e : G.edgeSet, if (e : Sym2 V) ∈ S.edgeSet then (if α e then 1 else 0) else 0

private lemma mstid_cost_eq_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (α : G.edgeSet → Bool) (S : SimpleGraph V) :
    mstid_cost G α S = ((Finset.univ : Finset G.edgeSet).filter
      (fun e : G.edgeSet => (e : Sym2 V) ∈ S.edgeSet ∧ α e = true)).card := by
  classical
  have h1 : mstid_cost G α S = ∑ e : G.edgeSet,
      (if ((e : Sym2 V) ∈ S.edgeSet ∧ α e = true) then (1:ℕ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro e _
    by_cases h : (e : Sym2 V) ∈ S.edgeSet <;> by_cases hb : α e <;> simp [h, hb]
  rw [h1, ← Finset.card_filter]

private lemma mstid_cost_swap {V : Type*} [Fintype V] (G T S : SimpleGraph V)
    (α : G.edgeSet → Bool) (remG addG : G.edgeSet)
    (hS : S.edgeSet = insert (addG : Sym2 V) (T.edgeSet \ {(remG : Sym2 V)}))
    (hrem : (remG : Sym2 V) ∈ T.edgeSet)
    (hαrem : α remG = true) (hαadd : α addG = false) :
    mstid_cost G α S = mstid_cost G α T - 1 := by
  classical
  rw [mstid_cost_eq_card, mstid_cost_eq_card]
  have hfil : ((Finset.univ : Finset G.edgeSet).filter
        (fun e : G.edgeSet => (e : Sym2 V) ∈ S.edgeSet ∧ α e = true)) =
      (((Finset.univ : Finset G.edgeSet).filter
        (fun e : G.edgeSet => (e : Sym2 V) ∈ T.edgeSet ∧ α e = true)).erase remG) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and]
    constructor
    · rintro ⟨hmem, hαx⟩
      rw [hS] at hmem
      rcases hmem with hx | ⟨hxt, hxne⟩
      · exfalso
        have hx' : x = addG := Subtype.ext hx
        rw [hx'] at hαx
        rw [hαx] at hαadd
        exact Bool.noConfusion hαadd
      · exact ⟨fun h => hxne (congrArg Subtype.val h), hxt, hαx⟩
    · rintro ⟨hxne, hxt, hαx⟩
      refine ⟨?_, hαx⟩
      rw [hS]
      exact Or.inr ⟨hxt, fun h => hxne (Subtype.ext h)⟩
  rw [hfil, Finset.card_erase_of_mem]
  simp [hrem, hαrem]

private lemma mstid_swap_edges {V : Type*} (T : SimpleGraph V) {e : Sym2 V} {a b : V}
    (hab : a ≠ b) :
    (T.deleteEdges {e} ⊔ SimpleGraph.edge a b).edgeSet =
      insert s(a, b) (T.edgeSet \ {e}) := by
  classical
  have hdiag : s(a, b) ∉ Sym2.diagSet := by simpa using hab
  have hsing : ({s(a, b)} : Set (Sym2 V)) \ Sym2.diagSet = {s(a, b)} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨And.left, fun hx => ⟨hx, fun hx' => hdiag (hx ▸ hx')⟩⟩
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_edge,
    hsing, Set.union_comm, Set.singleton_union]

private lemma mstid_swap_isTree
    {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    {e : Sym2 V} (he : e ∈ T.edgeSet) {a b : V} (hab : a ≠ b) (hne : s(a, b) ∉ T.edgeSet)
    (hnr : ¬ (T.deleteEdges {e}).Reachable a b) :
    (T.deleteEdges {e} ⊔ SimpleGraph.edge a b).IsTree := by
  classical
  have hacyc : (T.deleteEdges {e}).IsAcyclic := hT.isAcyclic.anti (SimpleGraph.deleteEdges_le _)
  have hSacyc : (T.deleteEdges {e} ⊔ SimpleGraph.edge a b).IsAcyclic :=
    hacyc.sup_edge_of_not_reachable hnr
  have h_edges := mstid_swap_edges (T := T) (e := e) (a := a) (b := b) hab
  rw [is_tree_iff_is_acyclic_and_card]
  refine ⟨hSacyc, ?_⟩
  have hcardT : Nat.card T.edgeSet + 1 = Nat.card V :=
    (is_tree_iff_is_acyclic_and_card T).mp hT |>.2
  have key : ((T.deleteEdges {e} ⊔ SimpleGraph.edge a b).edgeSet).ncard = T.edgeSet.ncard := by
    rw [h_edges, Set.ncard_insert_of_notMem (fun h => hne h.1)]
    exact Set.ncard_sdiff_singleton_add_one he
  rw [Nat.card_coe_set_eq, key, ← Nat.card_coe_set_eq]
  exact hcardT

private lemma mstid_path_edge_not_reachable {V : Type*} (T : SimpleGraph V) (hT : T.IsTree)
    {u v : V} (q : T.Walk u v) (hq : q.IsPath) {f : Sym2 V} (hf : f ∈ q.edges) :
    ¬ (T.deleteEdges {f}).Reachable u v := by
  classical
  have key : ∀ f : Sym2 V,
      ((T.deleteEdges {f}).Reachable u v ↔ ∃ p : T.Walk u v, f ∉ p.edges) :=
    fun f => @Sym2.ind V
      (fun g => ((T.deleteEdges {g}).Reachable u v ↔ ∃ p : T.Walk u v, g ∉ p.edges))
      (fun a b => SimpleGraph.reachable_deleteEdges_iff_exists_walk) f
  intro h
  rw [key f] at h
  obtain ⟨p, hp⟩ := h
  have huniq : (↑p.toPath : T.Walk u v) = q := (hT.existsUnique_path u v).unique p.toPath.isPath hq
  exact hp (SimpleGraph.Walk.edges_toPath_subset_edges p (huniq ▸ hf))

private lemma mstid_improve {V : Type*} [Fintype V] (G T S : SimpleGraph V)
    (α : G.edgeSet → Bool) (remG addG : G.edgeSet)
    (hSG : S ≤ G) (hS : S.IsTree) (hmin : is_mst_for G T α)
    (hSed : S.edgeSet = insert (addG : Sym2 V) (T.edgeSet \ {(remG : Sym2 V)}))
    (hrem : (remG : Sym2 V) ∈ T.edgeSet)
    (hαrem : α remG = true) (hαadd : α addG = false) : False := by
  have h1 : mstid_cost G α T ≤ mstid_cost G α S := hmin.2.2 S hSG hS
  have h2 : mstid_cost G α S = mstid_cost G α T - 1 :=
    mstid_cost_swap G T S α remG addG hSed hrem hαrem hαadd
  have hpos : 1 ≤ mstid_cost G α T := by
    rw [mstid_cost_eq_card]
    have hmem : remG ∈ ((Finset.univ : Finset G.edgeSet).filter
        (fun e : G.edgeSet => (e : Sym2 V) ∈ T.edgeSet ∧ α e = true)) := by
      simp [hrem, hαrem]
    exact Finset.card_pos.mpr ⟨remG, hmem⟩
  omega

private lemma mstid_alpha_lemmas {V : Type*} (G : SimpleGraph V)
    (β : G.edgeSet → Option Bool) (Z : Set (Sym2 V))
    (hZmem : ∀ x : G.edgeSet, ((x : Sym2 V) ∈ Z ↔ β x = some false))
    (remG addG : Sym2 V) (hneZ : remG ∉ Z) (hneadd : remG ≠ addG)
    (hDadd : ∀ x : G.edgeSet, β x = some true → (x : Sym2 V) ≠ addG) :
    (∀ (x : G.edgeSet) (b : Bool), β x = some b →
      (if (x : Sym2 V) ∈ Z ∨ (x : Sym2 V) = addG then false else true) = b) ∧
    ((if remG ∈ Z ∨ remG = addG then false else true) = true) ∧
    ((if addG ∈ Z ∨ addG = addG then false else true) = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x b hb
    by_cases h : (x : Sym2 V) ∈ Z ∨ (x : Sym2 V) = addG
    · rw [if_pos h]
      rcases h with h1 | h2
      · rw [(hZmem x).mp h1] at hb
        rw [Option.some.inj hb]
      · rcases b with _ | _
        · rfl
        · exact absurd hb (hDadd x · h2)
    · rw [if_neg h]
      rcases b with _ | _
      · exact absurd ((hZmem x).mpr hb) (fun hc => h (Or.inl hc))
      · rfl
  · rw [if_neg]
    exact fun hc => hc.elim hneZ hneadd
  · rw [if_pos (Or.inr rfl)]

private lemma mstid_subset_G {V : Type*} (G T : SimpleGraph V) (hTG : T ≤ G)
    {rem add : Sym2 V} (haddG : add ∈ G.edgeSet)
    {S : SimpleGraph V} (hS : S.edgeSet = insert add (T.edgeSet \ {rem})) : S ≤ G := by
  intro x y hxy
  have hx : s(x, y) ∈ S.edgeSet := hxy
  rw [hS] at hx
  rcases hx with rfl | ⟨hx, _⟩
  · exact haddG
  · exact SimpleGraph.edgeSet_mono hTG hx

open scoped Classical in
/-- If β certifies an MST, then every unqueried edge in the minor is a loop or bridge. -/
theorem mst_id_certificate_imp_minor_edges_loop_or_bridge {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (β : G.edgeSet → Option Bool)
    (hcert : is_mst_certificate G β) :
    ∀ (e : G.edgeSet), β e = none →
      minor_edge_is_loop G β e ∨ minor_edge_is_bridge G β e := by
  classical
  obtain ⟨T, hTG, hTtree, hTmin⟩ := hcert
  set Z : Set (Sym2 V) := {s | ∃ (h : s ∈ G.edgeSet), β ⟨s, h⟩ = some false} with hZdef
  set D : Set (Sym2 V) := {s | ∃ (h : s ∈ G.edgeSet), β ⟨s, h⟩ = some true} with hDdef
  have hZmem : ∀ x : G.edgeSet, ((x : Sym2 V) ∈ Z ↔ β x = some false) := by
    intro x
    refine ⟨?_, ?_⟩
    · rintro ⟨h, hb⟩
      rwa [show (⟨(x : Sym2 V), h⟩ : G.edgeSet) = x from Subtype.ext rfl] at hb
    · intro hb
      exact ⟨x.2, by rwa [show (⟨(x : Sym2 V), x.2⟩ : G.edgeSet) = x from Subtype.ext rfl]⟩
  have hDmem : ∀ x : G.edgeSet, ((x : Sym2 V) ∈ D ↔ β x = some true) := by
    intro x
    refine ⟨?_, ?_⟩
    · rintro ⟨h, hb⟩
      rwa [show (⟨(x : Sym2 V), h⟩ : G.edgeSet) = x from Subtype.ext rfl] at hb
    · intro hb
      exact ⟨x.2, by rwa [show (⟨(x : Sym2 V), x.2⟩ : G.edgeSet) = x from Subtype.ext rfl]⟩
  have key : ∀ (a b : V) (heG : s(a, b) ∈ G.edgeSet),
      β ⟨s(a, b), heG⟩ = none →
      minor_edge_is_loop G β ⟨s(a, b), heG⟩ ∨ minor_edge_is_bridge G β ⟨s(a, b), heG⟩ := by
    intro a b heG hnone
    by_cases hloop : minor_edge_is_loop G β ⟨s(a, b), heG⟩
    · exact Or.inl hloop
    · right
      have hab : a ≠ b := (SimpleGraph.mem_edgeSet G).mp heG |>.ne
      have hnZ : ¬ (SimpleGraph.fromEdgeSet Z).Reachable a b :=
        fun h => hloop ⟨a, b, rfl, h⟩
      have hzt : s(a, b) ∉ Z := by
        intro hc
        rw [(hZmem ⟨s(a, b), heG⟩).mp hc] at hnone
        exact absurd hnone (by simp)
      have hDz : ∀ x : G.edgeSet, β x = some true → (x : Sym2 V) ≠ s(a, b) := by
        intro x hx hc
        have hxD : (x : Sym2 V) ∈ D := (hDmem x).mpr hx
        rw [hc] at hxD
        rw [(hDmem ⟨s(a, b), heG⟩).mp hxD] at hnone
        exact absurd hnone (by simp)
      refine ⟨a, b, rfl, hnZ, ?_⟩
      intro hreach
      by_cases hmemT : s(a, b) ∈ T.edgeSet
      · have hbridge : T.IsBridge s(a, b) :=
          SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hTtree.isAcyclic
            ((SimpleGraph.mem_edgeSet T).mp hmemT)
        set S₀ : Set V := {v | (T.deleteEdges {s(a, b)}).Reachable a v} with hS₀
        have haS : a ∈ S₀ := SimpleGraph.Reachable.rfl
        have hbS : b ∉ S₀ := hbridge
        obtain ⟨p⟩ := hreach
        obtain ⟨d, hdmem, hdfst, hdsnd⟩ := p.exists_boundary_dart S₀ haS hbS
        have hgp : d.edge ∈ p.edges := by
          have h := List.mem_map_of_mem (f := SimpleGraph.Dart.edge) hdmem
          simpa [SimpleGraph.Walk.edges] using h
        have hgdel := SimpleGraph.Walk.edges_subset_edgeSet p hgp
        rw [SimpleGraph.edgeSet_deleteEdges] at hgdel
        have hgG : d.edge ∈ G.edgeSet := hgdel.1
        have hgnD : d.edge ∉ D := fun hc => hgdel.2 (Or.inr hc)
        have hgne : d.edge ≠ s(a, b) := fun hc => hgdel.2 (Or.inl hc)
        have huv_ne : d.toProd.1 ≠ d.toProd.2 := by
          intro hc
          exact hdsnd (hc ▸ hdfst)
        have hneT : d.edge ∉ T.edgeSet := by
          intro hT'
          have hTadj : T.Adj d.toProd.1 d.toProd.2 := (SimpleGraph.mem_edgeSet T).mp hT'
          have hadj : (T.deleteEdges {s(a, b)}).Adj d.toProd.1 d.toProd.2 := by
            rw [SimpleGraph.deleteEdges_adj]
            exact ⟨hTadj, hgne⟩
          exact hdsnd (hdfst.trans hadj.reachable)
        have hnr : ¬ (T.deleteEdges {s(a, b)}).Reachable d.toProd.1 d.toProd.2 :=
          fun hc => hdsnd (hdfst.trans hc)
        have hStree : (T.deleteEdges {s(a, b)} ⊔ SimpleGraph.edge d.toProd.1 d.toProd.2).IsTree :=
          mstid_swap_isTree (T := T) (e := s(a, b)) (a := d.toProd.1) (b := d.toProd.2)
            hTtree hmemT huv_ne hneT hnr
        have hSe : (T.deleteEdges {s(a, b)} ⊔ SimpleGraph.edge d.toProd.1 d.toProd.2).edgeSet =
            insert d.edge (T.edgeSet \ {s(a, b)}) :=
          mstid_swap_edges (T := T) (e := s(a, b)) (a := d.toProd.1) (b := d.toProd.2) huv_ne
        have hDg : ∀ x : G.edgeSet, β x = some true → (x : Sym2 V) ≠ d.edge := by
          intro x hx hc
          exact hgnD (hc ▸ ((hDmem x).mpr hx))
        have hα := mstid_alpha_lemmas G β Z hZmem s(a, b) d.edge hzt (Ne.symm hgne) hDg
        have hSG : (T.deleteEdges {s(a, b)} ⊔ SimpleGraph.edge d.toProd.1 d.toProd.2) ≤ G :=
          mstid_subset_G G T hTG hgG hSe
        exact mstid_improve G T _ _ ⟨s(a, b), heG⟩ ⟨d.edge, hgG⟩ hSG hStree
          (hTmin _ hα.1) hSe hmemT hα.2.1 hα.2.2
      · obtain ⟨q, hq⟩ := hTtree.connected.exists_isPath a b
        have hex : ∃ f, f ∈ q.edges ∧ f ∉ Z := by
          by_contra hc
          push Not at hc
          apply hnZ
          refine ⟨q.transfer (SimpleGraph.fromEdgeSet Z) ?_⟩
          intro f hf
          rw [SimpleGraph.edgeSet_fromEdgeSet]
          exact ⟨hc f hf,
            SimpleGraph.not_isDiag_of_mem_edgeSet (G := T)
              (SimpleGraph.Walk.edges_subset_edgeSet q hf)⟩
        obtain ⟨f, hfq, hfZ⟩ := hex
        have hfT : f ∈ T.edgeSet := SimpleGraph.Walk.edges_subset_edgeSet q hfq
        have hfG : f ∈ G.edgeSet := SimpleGraph.edgeSet_mono hTG hfT
        have hfe : f ≠ s(a, b) := fun hc => hmemT (hc ▸ hfT)
        have hnr : ¬ (T.deleteEdges {f}).Reachable a b :=
          mstid_path_edge_not_reachable T hTtree q hq hfq
        have hStree : (T.deleteEdges {f} ⊔ SimpleGraph.edge a b).IsTree :=
          mstid_swap_isTree (T := T) (e := f) (a := a) (b := b) hTtree hfT hab hmemT hnr
        have hSe : (T.deleteEdges {f} ⊔ SimpleGraph.edge a b).edgeSet =
            insert s(a, b) (T.edgeSet \ {f}) :=
          mstid_swap_edges (T := T) (e := f) (a := a) (b := b) hab
        have hα := mstid_alpha_lemmas G β Z hZmem f s(a, b) hfZ hfe hDz
        have hSG : (T.deleteEdges {f} ⊔ SimpleGraph.edge a b) ≤ G :=
          mstid_subset_G G T hTG heG hSe
        exact mstid_improve G T _ _ ⟨f, hfG⟩ ⟨s(a, b), heG⟩ hSG hStree
          (hTmin _ hα.1) hSe hfT hα.2.1 hα.2.2
  have key2 : ∀ (x : Sym2 V) (hx : x ∈ G.edgeSet), β ⟨x, hx⟩ = none →
      minor_edge_is_loop G β ⟨x, hx⟩ ∨ minor_edge_is_bridge G β ⟨x, hx⟩ := by
    intro x
    induction x using Sym2.inductionOn with
    | _ a b => exact key a b
  intro e he
  exact key2 (e : Sym2 V) e.2 he
