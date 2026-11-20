import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MatchingZeroCodegreeBlockedSwitchesForcesComplementFourCycle
import AFTD.Kb.Tcs.PerfectMatchingReplaceFinitePairedVertices
import AFTD.Kb.Tcs.Op2037SubgraphFintype

/-!
# minimally_k_extendable_high_degree_zero_codegree_complement_four_cycle

Topic: graphs   Node: b7c1e1b88c6d

Provenance: helper lemma. OP-1957: a stronger consequence of the general residual matching obstruction.

In a minimally k-extendable graph of minimum degree at least 2k+2, the complement neighborhoods of the endpoints of every zero-codegree graph edge contain a complete bipartite four-cycle.
-/

theorem in1063_fourcycle_tuple4_injective {V : Type*} (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [rfl, absurd hij hab, absurd hij hac, absurd hij had,
    absurd hij hab.symm, rfl, absurd hij hbc, absurd hij hbd,
    absurd hij hac.symm, absurd hij hbc.symm, rfl, absurd hij hcd,
    absurd hij had.symm, absurd hij hbd.symm, absurd hij hcd.symm, rfl]

theorem in1063_fourcycle_tuple6_injective {V : Type*} (a b c d e f : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Injective (![a,b,c,d,e,f] : Fin 6 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [rfl, absurd hij hab, absurd hij hac, absurd hij had, absurd hij hae, absurd hij haf,
    absurd hij hab.symm, rfl, absurd hij hbc, absurd hij hbd, absurd hij hbe, absurd hij hbf,
    absurd hij hac.symm, absurd hij hbc.symm, rfl, absurd hij hcd, absurd hij hce, absurd hij hcf,
    absurd hij had.symm, absurd hij hbd.symm, absurd hij hcd.symm, rfl, absurd hij hde, absurd hij hdf,
    absurd hij hae.symm, absurd hij hbe.symm, absurd hij hce.symm, absurd hij hde.symm, rfl, absurd hij hef,
    absurd hij haf.symm, absurd hij hbf.symm, absurd hij hcf.symm, absurd hij hdf.symm, absurd hij hef.symm, rfl]

theorem in1063_residual_four_cycle
    {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching) (R : Set V)
    (hcl : ∀ a b, P.Adj a b → a ∉ R → b ∉ R)
    (u v : V) (huv : P.Adj u v)
    (hdeg_u : ∃ x y : V, x ≠ y ∧ x ∉ R ∧ y ∉ R ∧ G.Adj u x ∧ G.Adj u y)
    (hdeg_v : ∃ x y : V, x ≠ y ∧ x ∉ R ∧ y ∉ R ∧ G.Adj v x ∧ G.Adj v y)
    (hfar2 : ∀ x : V, ¬ ((Gᶜ).Adj u x ∧ (Gᶜ).Adj v x))
    (h4 : ¬ ∃ a b, a ∉ R ∧ b ∉ R ∧ Function.Injective (![u,v,a,b] : Fin 4 → V) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b)
    (h6 : ¬ ∃ a b c d, a ∉ R ∧ b ∉ R ∧ c ∉ R ∧ d ∉ R ∧ Function.Injective (![u,v,a,b,c,d] : Fin 6 → V) ∧ P.Adj a b ∧ P.Adj c d ∧ G.Adj v b ∧ G.Adj a c ∧ G.Adj u d) :
    ∃ a b c d, Function.Injective (![u,v,a,b,c,d] : Fin 6 → V) ∧
      (Gᶜ).Adj u a ∧ (Gᶜ).Adj u b ∧ (Gᶜ).Adj v c ∧ (Gᶜ).Adj v d ∧
      (Gᶜ).Adj a c ∧ (Gᶜ).Adj a d ∧ (Gᶜ).Adj b c ∧ (Gᶜ).Adj b d
:= by
  classical
  have hmate : ∀ {a b c : V}, P.Adj a b → P.Adj a c → b = c :=
    fun {a b c} h1 h2 => (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP a).unique h1 h2
  have huvG : G.Adj u v := P.adj_sub huv
  have huvne : u ≠ v := huvG.ne
  have choose_other (s t : V) (h : ∃ x y : V, x ≠ y ∧ x ∉ R ∧ y ∉ R ∧ G.Adj s x ∧ G.Adj s y) :
      ∃ z, z ≠ t ∧ z ∉ R ∧ G.Adj s z := by
    obtain ⟨x,y,hxy,hxR,hyR,hx,hy⟩ := h
    by_cases hxt : x = t
    · refine ⟨y, ?_, hyR, hy⟩
      intro hyt
      exact hxy (hxt.trans hyt.symm)
    · exact ⟨x,hxt,hxR,hx⟩
  have hnu (x : V) (hxu : x ≠ u) (hxv : x ≠ v) (hux : ¬ G.Adj u x) : G.Adj v x := by
    by_contra hvx
    apply hfar2 x
    exact ⟨(SimpleGraph.compl_adj G u x).2 ⟨hxu.symm,hux⟩,
      (SimpleGraph.compl_adj G v x).2 ⟨hxv.symm,hvx⟩⟩
  have hnv (x : V) (hxu : x ≠ u) (hxv : x ≠ v) (hvx : ¬ G.Adj v x) : G.Adj u x := by
    by_contra hux
    apply hfar2 x
    exact ⟨(SimpleGraph.compl_adj G u x).2 ⟨hxu.symm,hux⟩,
      (SimpleGraph.compl_adj G v x).2 ⟨hxv.symm,hvx⟩⟩
  obtain ⟨x,hxu,hxR,hvx⟩ := choose_other v u hdeg_v
  have hxv : x ≠ v := hvx.symm.ne
  obtain ⟨y,hxy,_⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) x
  have hyR : y ∉ R := hcl x y hxy hxR
  have hxyne : x ≠ y := (P.adj_sub hxy).ne
  have hyu : y ≠ u := by
    intro h
    subst y
    have h' : v = x := hmate huv hxy.symm
    exact hxv h'.symm
  have hyv : y ≠ v := by
    intro h
    subst y
    have h' : u = x := hmate huv.symm hxy.symm
    exact hxu h'.symm
  have huxy : ¬ G.Adj u y := by
    intro h
    apply h4
    refine ⟨x,y,hxR,hyR,?_,hxy,hvx,h⟩
    exact in1063_fourcycle_tuple4_injective u v x y huvne hxu.symm hyu.symm hxv.symm hyv.symm hxyne
  have hvy : G.Adj v y := hnu y hyu hyv huxy
  have huxx : ¬ G.Adj u x := by
    intro h
    apply h4
    refine ⟨y,x,hyR,hxR,?_,hxy.symm,hvy,h⟩
    exact in1063_fourcycle_tuple4_injective u v y x huvne hyu.symm hxu.symm hyv.symm hxv.symm hxyne.symm
  obtain ⟨z,hzv,hzR,huz⟩ := choose_other u v hdeg_u
  have hzu : z ≠ u := huz.symm.ne
  obtain ⟨t,hzt,_⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) z
  have htR : t ∉ R := hcl z t hzt hzR
  have hztne : z ≠ t := (P.adj_sub hzt).ne
  have htu : t ≠ u := by
    intro h
    subst t
    have h' : v = z := hmate huv hzt.symm
    exact hzv h'.symm
  have htv : t ≠ v := by
    intro h
    subst t
    have h' : u = z := hmate huv.symm hzt.symm
    exact hzu h'.symm
  have hvt : ¬ G.Adj v t := by
    intro h
    apply h4
    refine ⟨t,z,htR,hzR,?_,hzt.symm,h,huz⟩
    exact in1063_fourcycle_tuple4_injective u v t z huvne htu.symm hzu.symm htv.symm hzv.symm hztne.symm
  have hut : G.Adj u t := hnv t htu htv hvt
  have hvz : ¬ G.Adj v z := by
    intro h
    apply h4
    refine ⟨z,t,hzR,htR,?_,hzt,h,hut⟩
    exact in1063_fourcycle_tuple4_injective u v z t huvne hzu.symm htu.symm hzv.symm htv.symm hztne
  have hxz : x ≠ z := by
    intro h
    subst z
    exact hvz hvx
  have hxt : x ≠ t := by
    intro h
    subst t
    exact hvt hvx
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hvz hvy
  have hyt : y ≠ t := by
    intro h
    subst t
    exact hvt hvy
  have hxzH : ¬ G.Adj x z := by
    intro h
    apply h6
    refine ⟨x,y,z,t,hxR,hyR,hzR,htR,?_,hxy,hzt,hvy,h,hut⟩
    exact in1063_fourcycle_tuple6_injective u v x y z t huvne hxu.symm hyu.symm hzu.symm htu.symm
      hxv.symm hyv.symm hzv.symm htv.symm hxyne hxz hxt hyz hyt hztne
  have hxtH : ¬ G.Adj x t := by
    intro h
    apply h6
    refine ⟨x,y,t,z,hxR,hyR,htR,hzR,?_,hxy,hzt.symm,hvy,h,huz⟩
    exact in1063_fourcycle_tuple6_injective u v x y t z huvne hxu.symm hyu.symm htu.symm hzu.symm
      hxv.symm hyv.symm htv.symm hzv.symm hxyne hxt hxz hyt hyz hztne.symm
  have hyzH : ¬ G.Adj y z := by
    intro h
    apply h6
    refine ⟨y,x,z,t,hyR,hxR,hzR,htR,?_,hxy.symm,hzt,hvx,h,hut⟩
    exact in1063_fourcycle_tuple6_injective u v y x z t huvne hyu.symm hxu.symm hzu.symm htu.symm
      hyv.symm hxv.symm hzv.symm htv.symm hxyne.symm hyz hyt hxz hxt hztne
  have hytH : ¬ G.Adj y t := by
    intro h
    apply h6
    refine ⟨y,x,t,z,hyR,hxR,htR,hzR,?_,hxy.symm,hzt.symm,hvx,h,huz⟩
    exact in1063_fourcycle_tuple6_injective u v y x t z huvne hyu.symm hxu.symm htu.symm hzu.symm
      hyv.symm hxv.symm htv.symm hzv.symm hxyne.symm hyt hyz hxt hxz hztne.symm
  refine ⟨x,y,z,t,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact in1063_fourcycle_tuple6_injective u v x y z t huvne hxu.symm hyu.symm hzu.symm htu.symm
      hxv.symm hyv.symm hzv.symm htv.symm hxyne hxz hxt hyz hyt hztne
  · exact (SimpleGraph.compl_adj G u x).2 ⟨hxu.symm,huxx⟩
  · exact (SimpleGraph.compl_adj G u y).2 ⟨hyu.symm,huxy⟩
  · exact (SimpleGraph.compl_adj G v z).2 ⟨hzv.symm,hvz⟩
  · exact (SimpleGraph.compl_adj G v t).2 ⟨htv.symm,hvt⟩
  · exact (SimpleGraph.compl_adj G x z).2 ⟨hxz,hxzH⟩
  · exact (SimpleGraph.compl_adj G x t).2 ⟨hxt,hxtH⟩
  · exact (SimpleGraph.compl_adj G y z).2 ⟨hyz,hyzH⟩
  · exact (SimpleGraph.compl_adj G y t).2 ⟨hyt,hytH⟩

theorem in1063_transport {V : Type*} (G : SimpleGraph V) (u v : V)
    (M : (G.deleteEdges {s(u,v)}).Subgraph) (Q : G.Subgraph) (hQ : Q.IsPerfectMatching)
    (hMQv : M.verts ⊆ Q.verts) (hMQ : ∀ x y, M.Adj x y → Q.Adj x y) (hno : ¬ Q.Adj u v) :
    ∃ P : (G.deleteEdges {s(u,v)}).Subgraph, P.IsPerfectMatching ∧ M ≤ P := by
  have hsub : ∀ {x y : V}, Q.Adj x y → (G.deleteEdges {s(u,v)}).Adj x y := by
    intro x y h
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨Q.adj_sub h, ?_⟩
    intro he
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hno h
    · exact hno h.symm
  refine ⟨⟨Q.verts, Q.Adj, hsub, Q.edge_vert, Q.symm⟩, ⟨fun x hx => hQ.1 hx, fun x => hQ.2 x⟩, ?_⟩
  exact ⟨hMQv, fun {x y} h => hMQ x y h⟩

theorem in1063_verts_bound {n k : ℕ} {H : SimpleGraph (Fin n)} (M : H.Subgraph) (hM : M.IsMatching)
    (hMk : M.edgeSet.ncard = k) :
    ∃ S : Finset (Fin n), (∀ x, x ∈ M.verts → x ∈ S) ∧ S.card ≤ 2 * k := by
  classical
  refine ⟨(M.edgeSet.toFinite.toFinset).biUnion (fun e => e.toFinset), ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, -⟩ := hM hx
    rw [Finset.mem_biUnion]
    exact ⟨s(x, w), by simpa using hw, by simp⟩
  · have h1 : ((M.edgeSet.toFinite.toFinset).biUnion (fun e => e.toFinset)).card ≤
        (M.edgeSet.toFinite.toFinset).card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro e _
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    have h2 : (M.edgeSet.toFinite.toFinset).card = k := by
      rw [← Set.ncard_eq_toFinset_card M.edgeSet M.edgeSet.toFinite, hMk]
    omega

theorem minimally_k_extendable_high_degree_zero_codegree_complement_four_cycle
    (k n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (hdegree : 2*k+2 ≤ G.minDegree)
    (u v : Fin n) (huv : G.Adj u v)
    (hfar2 : ∀ x, ¬ ((Gᶜ).Adj u x ∧ (Gᶜ).Adj v x)) :
    ∃ a b c d, Function.Injective (![u,v,a,b,c,d] : Fin 6 → Fin n) ∧
      (Gᶜ).Adj u a ∧ (Gᶜ).Adj u b ∧ (Gᶜ).Adj v c ∧ (Gᶜ).Adj v d ∧
      (Gᶜ).Adj a c ∧ (Gᶜ).Adj a d ∧ (Gᶜ).Adj b c ∧ (Gᶜ).Adj b d := by
  classical
  obtain ⟨⟨hcard, ⟨M0, hM0, hM0k⟩, hext⟩, hminimal⟩ := hmin
  have hG' : ∀ x y : Fin n, (G.deleteEdges {s(u, v)}).Adj x y ↔ G.Adj x y ∧ s(x, y) ≠ s(u, v) := by
    intro x y
    simp [SimpleGraph.deleteEdges_adj]
  have hsym : ∀ x y : Fin n, s(x, y) = s(u, v) → (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    intro x y h
    simpa [Sym2.eq_iff] using h
  have huvne : u ≠ v := huv.ne
  -- (b) a k-matching of G - uv
  have hb : ∃ M : (G.deleteEdges {s(u, v)}).Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k := by
    have hM0u : ∀ {x y y' : Fin n}, M0.Adj x y → M0.Adj x y' → y = y' := by
      intro x y y' h h'
      exact (hM0 (M0.edge_vert h)).unique h h'
    by_cases hM0uv : M0.Adj u v
    · obtain ⟨P0, hP0, hM0P0⟩ := hext M0 hM0 hM0k
      have hP0' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP0
      obtain ⟨S0, hS0, hS0c⟩ := in1063_verts_bound M0 hM0 hM0k
      obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ S0 := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        have h1 : S0 = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
        rw [h1, Finset.card_univ] at hS0c
        omega
      have hwM : w ∉ M0.verts := fun h => hw (hS0 w h)
      obtain ⟨w', hww', -⟩ := hP0' w
      have hw'M : w' ∉ M0.verts := by
        intro h
        obtain ⟨c, hc, -⟩ := hM0 h
        have : c = w := (hP0' w').unique (hM0P0.2 hc) hww'.symm
        exact hwM (this ▸ M0.edge_vert hc.symm)
      have hwne : w ≠ w' := (P0.adj_sub hww').ne
      have huM : u ∈ M0.verts := M0.edge_vert hM0uv
      have hvM : v ∈ M0.verts := M0.edge_vert hM0uv.symm
      have hwu : w ≠ u := fun h => hwM (h ▸ huM)
      have hwv : w ≠ v := fun h => hwM (h ▸ hvM)
      -- an M0-edge other than uv avoids u and v
      have hoff : ∀ {x y : Fin n}, M0.Adj x y → s(x, y) ≠ s(u, v) → x ≠ u ∧ x ≠ v := by
        intro x y hxy hne
        constructor
        · rintro rfl
          exact hne (by rw [hM0u hxy hM0uv])
        · rintro rfl
          exact hne (by rw [hM0u hxy hM0uv.symm]; exact Sym2.eq_swap)
      let M1 : (G.deleteEdges {s(u, v)}).Subgraph :=
        { verts := (M0.verts \ {u, v}) ∪ {w, w'}
          Adj := fun x y => (M0.Adj x y ∧ s(x, y) ≠ s(u, v)) ∨ (x = w ∧ y = w') ∨ (x = w' ∧ y = w)
          adj_sub := by
            rintro x y (⟨h, hne⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact (hG' x y).mpr ⟨M0.adj_sub h, hne⟩
            · refine (hG' _ _).mpr ⟨P0.adj_sub hww', fun he => ?_⟩
              rcases hsym _ _ he with ⟨h1, -⟩ | ⟨h1, -⟩
              · exact hwu h1
              · exact hwv h1
            · refine (hG' _ _).mpr ⟨P0.adj_sub hww'.symm, fun he => ?_⟩
              rcases hsym _ _ he with ⟨-, h1⟩ | ⟨-, h1⟩
              · exact hwv h1
              · exact hwu h1
          edge_vert := by
            rintro x y (⟨h, hne⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · obtain ⟨h1, h2⟩ := hoff h hne
              exact Or.inl ⟨M0.edge_vert h, by simp [h1, h2]⟩
            · exact Or.inr (by simp)
            · exact Or.inr (by simp)
          symm := by
            refine ⟨?_⟩
            rintro x y (⟨h, hne⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact Or.inl ⟨h.symm, by rwa [Sym2.eq_swap]⟩
            · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩) }
      refine ⟨M1, ?_, ?_⟩
      · intro x hx
        rcases hx with ⟨hx0, hxuv⟩ | hxw
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxuv
          obtain ⟨y, hy, -⟩ := hM0 hx0
          have hne : s(x, y) ≠ s(u, v) := by
            intro he
            rcases hsym _ _ he with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hxuv.1 h1
            · exact hxuv.2 h1
          refine ⟨y, Or.inl ⟨hy, hne⟩, ?_⟩
          rintro y' (⟨h', -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hM0u h' hy
          · exact absurd hx0 hwM
          · exact absurd hx0 hw'M
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxw
          rcases hxw with rfl | rfl
          · refine ⟨w', Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
            rintro y' (⟨h', -⟩ | ⟨-, rfl⟩ | ⟨h1, -⟩)
            · exact absurd (M0.edge_vert h') hwM
            · rfl
            · exact absurd h1 hwne
          · refine ⟨w, Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
            rintro y' (⟨h', -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩)
            · exact absurd (M0.edge_vert h') hw'M
            · exact absurd h1.symm hwne
            · rfl
      · have hE : M1.edgeSet = (M0.edgeSet \ {s(u, v)}) ∪ {s(w, w')} := by
          ext e
          induction e using Sym2.ind with
          | h x y =>
            simp only [SimpleGraph.Subgraph.mem_edgeSet, Set.mem_union, Set.mem_sdiff,
              Set.mem_singleton_iff]
            show ((M0.Adj x y ∧ s(x, y) ≠ s(u, v)) ∨ (x = w ∧ y = w') ∨ (x = w' ∧ y = w)) ↔ _
            simp only [Sym2.eq_iff, ne_eq]
        have hdisj : Disjoint (M0.edgeSet \ {s(u, v)}) {s(w, w')} := by
          rw [Set.disjoint_singleton_right]
          rintro ⟨h, -⟩
          exact hwM (M0.edge_vert h)
        have hmem : s(u, v) ∈ M0.edgeSet := hM0uv
        rw [hE, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
          Set.ncard_sdiff_singleton_of_mem hmem, Set.ncard_singleton, hM0k]
        have hpos : 0 < M0.edgeSet.ncard := Set.ncard_pos (Set.toFinite _) |>.mpr ⟨_, hmem⟩
        omega
    · refine ⟨⟨M0.verts, M0.Adj, fun {x y} h => (hG' x y).mpr ⟨M0.adj_sub h, fun he => ?_⟩,
        M0.edge_vert, M0.symm⟩, fun x hx => hM0 hx, ?_⟩
      · rcases hsym _ _ he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hM0uv h
        · exact hM0uv h.symm
      · refine Eq.trans (congrArg Set.ncard ?_) hM0k
        ext e; induction e using Sym2.ind; exact Iff.rfl
  -- a non-extendable k-matching of G - uv
  have hnot := hminimal s(u, v) (by simpa using huv)
  obtain ⟨M, hM, hMk, hMno⟩ : ∃ M : (G.deleteEdges {s(u, v)}).Subgraph, M.IsMatching ∧
      M.edgeSet.ncard = k ∧ ¬ ∃ P : (G.deleteEdges {s(u, v)}).Subgraph, P.IsPerfectMatching ∧ M ≤ P := by
    by_contra hcon
    push Not at hcon
    exact hnot ⟨hcard, hb, fun M hM hk => hcon M hM hk⟩
  have hup : ∀ {x y : Fin n}, M.Adj x y → G.Adj x y := fun h => ((hG' _ _).mp (M.adj_sub h)).1
  let MG : G.Subgraph := ⟨M.verts, M.Adj, hup, M.edge_vert, M.symm⟩
  have hMG : MG.IsMatching := fun x hx => hM hx
  have hMGk : MG.edgeSet.ncard = k :=
    Eq.trans (congrArg Set.ncard (by ext e; induction e using Sym2.ind; exact Iff.rfl)) hMk
  obtain ⟨P, hP, hMP⟩ := hext MG hMG hMGk
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  have hMPadj : ∀ {x y : Fin n}, M.Adj x y → P.Adj x y := fun h => hMP.2 h
  have hPuv : P.Adj u v := by
    by_contra h
    exact hMno (in1063_transport G u v M P hP hMP.1 (fun x y hxy => hMPadj hxy) h)
  have hnotin : ∀ x, (x = u ∨ x = v) → x ∉ M.verts := by
    intro x hx hxM
    obtain ⟨y, hy, -⟩ := hM hxM
    have hPy := hMPadj hy
    rcases hx with rfl | rfl
    · have : y = v := (hP' x).unique hPy hPuv
      subst this
      exact ((hG' _ _).mp (M.adj_sub hy)).2 rfl
    · have : y = u := (hP' x).unique hPy hPuv.symm
      subst this
      exact ((hG' _ _).mp (M.adj_sub hy)).2 Sym2.eq_swap
  have huR : u ∉ M.verts := hnotin u (Or.inl rfl)
  have hvR : v ∉ M.verts := hnotin v (Or.inr rfl)
  have hcl : ∀ a b, P.Adj a b → a ∉ M.verts → b ∉ M.verts := by
    intro a b hab ha hbM
    obtain ⟨c, hc, -⟩ := hM hbM
    have : c = a := (hP' b).unique (hMPadj hc) hab.symm
    exact ha (this ▸ M.edge_vert hc.symm)
  obtain ⟨S, hS, hSc⟩ := in1063_verts_bound MG hMG hMGk
  have hdeg2 : ∀ x : Fin n, ∃ a b : Fin n, a ≠ b ∧ a ∉ M.verts ∧ b ∉ M.verts ∧ G.Adj x a ∧ G.Adj x b := by
    intro x
    have h1 : 2 * k + 2 ≤ (G.neighborFinset x).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact le_trans hdegree (G.minDegree_le_degree x)
    have h2 : 1 < (G.neighborFinset x \ S).card := by
      have := Finset.le_card_sdiff S (G.neighborFinset x)
      omega
    obtain ⟨a, ha, b, hb', hab⟩ := Finset.one_lt_card.mp h2
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at ha hb'
    exact ⟨a, b, hab, fun h => ha.2 (hS a h), fun h => hb'.2 (hS b h), ha.1, hb'.1⟩
  have hMQ : ∀ (Q : G.Subgraph), MG ≤ Q → ∀ x y, M.Adj x y → Q.Adj x y :=
    fun Q h x y hxy => h.2 hxy
  apply in1063_residual_four_cycle G P hP M.verts hcl u v hPuv (hdeg2 u) (hdeg2 v) hfar2
  · rintro ⟨a, b, haR, hbR, hinj, hab, hva, hub⟩
    apply hMno
    obtain ⟨Q, hQ, hMQle, hQσ⟩ := perfect_matching_replace_finite_paired_vertices G P MG hP hMP 4
      ![u, v, a, b] hinj ![1, 0, 3, 2] ![3, 2, 1, 0]
      (by intro i; fin_cases i <;> simp [hPuv, hPuv.symm, hab, hab.symm])
      (by decide)
      (by intro i; fin_cases i <;> simp [hva, hub, hva.symm, hub.symm])
      (by intro i; fin_cases i <;> simp [MG, huR, hvR, haR, hbR])
    have hQub : Q.Adj u b := by simpa using hQσ 0
    have hbv : b ≠ v := fun h => absurd (hinj (show ![u, v, a, b] 3 = ![u, v, a, b] 1 by simp [h])) (by decide)
    have hQ' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hQ
    exact in1063_transport G u v M Q hQ hMQle.1 (hMQ Q hMQle)
      (fun h => hbv ((hQ' u).unique hQub h))
  · rintro ⟨a, b, c, d, haR, hbR, hcR, hdR, hinj, hab, hcd, hvb, hac, hud⟩
    apply hMno
    obtain ⟨Q, hQ, hMQle, hQσ⟩ := perfect_matching_replace_finite_paired_vertices G P MG hP hMP 6
      ![u, v, a, b, c, d] hinj ![1, 0, 3, 2, 5, 4] ![5, 3, 4, 1, 2, 0]
      (by intro i; fin_cases i <;> simp [hPuv, hPuv.symm, hab, hab.symm, hcd, hcd.symm])
      (by decide)
      (by intro i; fin_cases i <;> simp [hvb, hac, hud, hvb.symm, hac.symm, hud.symm])
      (by intro i; fin_cases i <;> simp [MG, huR, hvR, haR, hbR, hcR, hdR])
    have hQud : Q.Adj u d := by simpa using hQσ 0
    have hdv : d ≠ v := fun h => absurd (hinj (show ![u, v, a, b, c, d] 5 = ![u, v, a, b, c, d] 1 by simp [h])) (by decide)
    have hQ' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hQ
    exact in1063_transport G u v M Q hQ hMQle.1 (hMQ Q hMQle)
      (fun h => hdv ((hQ' u).unique hQud h))
