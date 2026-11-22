import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeCommonNonneighborsBelowMinDegreeIsBridge
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.Supp

/-!
# forced_matching_edge_barrier_component_partition

Topic: graphs   Node: 8c1e64b0b5e7

Provenance: helper lemma. OP-1957; general component bookkeeping for the saturated-block boundary reduction.

A perfect-matchable finite graph with a forced edge that has an alternate path admits the displayed nonempty barrier and component partition: the only possible edge between the endpoint components is the forced edge, the remaining part is anticomplete to both, and it has at least as many odd components as the barrier has vertices.
-/

theorem barrier_odd_component_matched_outside
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (S₀ : Set V) (M : G.Subgraph) (hM : M.IsPerfectMatching)
    (c : ((⊤ : (G.deleteEdges {s(u,v)}).Subgraph).deleteVerts S₀).coe.ConnectedComponent)
    (hodd : Odd c.supp.ncard) (havoid : ∀ a ∈ c.supp, a.1 ≠ u ∧ a.1 ≠ v) :
    ∃ w ∈ S₀, ∃ a ∈ c.supp, M.Adj a.1 w := by
  classical
  by_contra hno
  push Not at hno
  let C : Set V := Subtype.val '' c.supp
  have hmatch : (M.induce C).IsMatching := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b, hab, huniq⟩ := hM.1 (hM.2 a'.1)
    have hbS : b ∉ S₀ := fun hb => hno b hb a' ha' hab
    have hbK : b ∈ ((⊤ : (G.deleteEdges {s(u,v)}).Subgraph).deleteVerts S₀).verts := by
      simp [hbS]
    have hG' : (G.deleteEdges {s(u,v)}).Adj a'.1 b := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨M.adj_sub hab, ?_⟩
      intro he
      simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he
      rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact (havoid a' ha').1 h1
      · exact (havoid a' ha').2 h1
    have hadj : ((⊤ : (G.deleteEdges {s(u,v)}).Subgraph).deleteVerts S₀).coe.Adj a' ⟨b, hbK⟩ := by
      have ha'S : a'.1 ∉ S₀ := by have := a'.2; simpa using this
      have h2 := hG'
      simp at h2 ⊢
      exact ⟨ha'S, hbS, h2⟩
    have hbc : (⟨b, hbK⟩ : ((⊤ : (G.deleteEdges {s(u,v)}).Subgraph).deleteVerts S₀).verts) ∈ c.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha' ⊢
      rw [← ha']
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
    refine ⟨b, ⟨⟨a', ha', rfl⟩, ⟨⟨b, hbK⟩, hbc, rfl⟩, hab⟩, fun y hy => huniq y hy.2.2⟩
  have hfin : Fintype (M.induce C).verts := Fintype.ofFinite _
  have he := hmatch.even_card
  rw [← Set.ncard_eq_toFinset_card'] at he
  have hC : (M.induce C).verts.ncard = c.supp.ncard := by
    show C.ncard = _
    exact Set.ncard_image_of_injective _ Subtype.val_injective
  rw [hC] at he
  exact (Nat.not_even_iff_odd.mpr hodd) he

theorem forced_matching_edge_barrier_component_partition
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : G.Adj u v)
    (hP : ∃ P : G.Subgraph, P.IsPerfectMatching)
    (hforced : ¬ ∃ P : (G.deleteEdges {s(u,v)}).Subgraph, P.IsPerfectMatching)
    (hpath : (G.deleteEdges {s(u,v)}).Reachable u v) :
    ∃ S X Y U : Finset V,
      S.Nonempty ∧ Disjoint S X ∧ Disjoint S Y ∧ Disjoint S U ∧
      Disjoint X Y ∧ Disjoint X U ∧ Disjoint Y U ∧
      S ∪ X ∪ Y ∪ U = Finset.univ ∧ u ∈ X ∧ v ∈ Y ∧
      (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y → x = u ∧ y = v) ∧
      (∀ w ∈ U, ∀ z ∈ X ∪ Y, ¬ G.Adj w z) ∧
      S.card ≤ (G.induce {a | a ∈ U}).oddComponents.ncard := by
  classical
  obtain ⟨M, hM⟩ := hP
  obtain ⟨S₀, hviol⟩ : ∃ S₀ : Set V, (G.deleteEdges {s(u,v)}).IsTutteViolator S₀ := by
    by_contra h
    push Not at h
    exact hforced (SimpleGraph.tutte.mpr h)
  set K := (⊤ : (G.deleteEdges {s(u,v)}).Subgraph).deleteVerts S₀ with hKdef
  set H := K.coe with hHdef
  have hviol' : S₀.ncard < H.oddComponents.ncard := hviol
  have hKmem : ∀ a : V, a ∈ K.verts ↔ a ∉ S₀ := by intro a; simp [K]
  have hG'adj : ∀ a b : V, s(a,b) ≠ s(u,v) → G.Adj a b → (G.deleteEdges {s(u,v)}).Adj a b := by
    intro a b hne hab
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hab, by simpa using hne⟩
  have hHadj : ∀ a b : K.verts, (G.deleteEdges {s(u,v)}).Adj a.1 b.1 → H.Adj a b := by
    intro a b h
    have ha := (hKmem a.1).mp a.2
    have hb := (hKmem b.1).mp b.2
    have h2 := h
    simp at h2 ⊢
    exact ⟨a.2, b.2, h⟩
  have hHadj' : ∀ a b : K.verts, H.Adj a b → G.Adj a.1 b.1 := by
    intro a b h
    have h2 := h
    simp [H, K] at h2
    exact h2.2.2.1
  -- parity
  have hEven : Even (Fintype.card V) := hM.even_card
  have hpar := (SimpleGraph.odd_ncard_oddComponents (G := H))
  have hcardK : Nat.card K.verts + S₀.ncard = Fintype.card V := by
    rw [Nat.card_coe_set_eq]
    have hKv : K.verts = S₀ᶜ := by ext a; simp [hKmem]
    rw [hKv, add_comm, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have hge : S₀.ncard + 2 ≤ H.oddComponents.ncard := by
    obtain ⟨N, hN⟩ := hEven
    rcases Nat.even_or_odd H.oddComponents.ncard with hn | hn
    · have ht : ¬ Odd (Nat.card K.verts) := fun h => (Nat.not_odd_iff_even.mpr hn) (hpar.mpr h)
      obtain ⟨t, htt⟩ := Nat.not_odd_iff_even.mp ht
      obtain ⟨n, hnn⟩ := hn
      omega
    · obtain ⟨t, htt⟩ := hpar.mp hn
      obtain ⟨n, hnn⟩ := hn
      omega
  -- the components meeting u or v
  let Bset : Set H.ConnectedComponent := {c | ∃ a ∈ c.supp, a.1 = u ∨ a.1 = v}
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard H.oddComponents Bset (Set.toFinite _)
  have hkey : ∀ c ∈ H.oddComponents \ Bset, ∃ w ∈ S₀, ∃ a ∈ c.supp, M.Adj a.1 w := by
    intro c hc
    refine barrier_odd_component_matched_outside G u v S₀ M hM c hc.1 ?_
    intro a ha
    have := hc.2
    simp only [Bset, Set.mem_setOf_eq, not_exists, not_and, not_or] at this
    exact this a ha
  let f : H.ConnectedComponent → V := fun c =>
    if h : c ∈ H.oddComponents \ Bset then (hkey c h).choose else u
  have hfS : ∀ c ∈ H.oddComponents \ Bset, f c ∈ S₀ := by
    intro c hc
    simp only [f, dif_pos hc]
    exact (hkey c hc).choose_spec.1
  have hfinj : Set.InjOn f (H.oddComponents \ Bset) := by
    intro c1 hc1 c2 hc2 heq
    obtain ⟨-, a1, ha1, hm1⟩ := (hkey c1 hc1).choose_spec
    obtain ⟨-, a2, ha2, hm2⟩ := (hkey c2 hc2).choose_spec
    have e1 : f c1 = (hkey c1 hc1).choose := by simp only [f, dif_pos hc1]
    have e2 : f c2 = (hkey c2 hc2).choose := by simp only [f, dif_pos hc2]
    rw [← e1] at hm1
    rw [← e2, ← heq] at hm2
    have hw : f c1 ∈ M.verts := M.edge_vert hm1.symm
    have h12 : a1.1 = a2.1 := (hM.1 hw).unique hm1.symm hm2.symm
    have : a1 = a2 := Subtype.ext h12
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha1 ha2
    rw [← ha1, ← ha2, this]
  have hA : (H.oddComponents \ Bset).ncard ≤ S₀.ncard :=
    Set.ncard_le_ncard_of_injOn f hfS hfinj (Set.toFinite _)
  have hB2 : 1 < (H.oddComponents ∩ Bset).ncard := by omega
  obtain ⟨c1, c2, hc1, hc2, hc12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hB2
  obtain ⟨a1, ha1, hb1⟩ := hc1.2
  obtain ⟨a2, ha2, hb2⟩ := hc2.2
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha1 ha2
  have hdist : ∀ (hu : u ∈ K.verts) (hv : v ∈ K.verts),
      H.connectedComponentMk ⟨u,hu⟩ = H.connectedComponentMk ⟨v,hv⟩ → False := by
    intro hu hv he
    apply hc12
    rw [← ha1, ← ha2]
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · rw [show a1 = a2 from Subtype.ext (h1.trans h2.symm)]
    · rw [show a1 = ⟨u,hu⟩ from Subtype.ext h1, show a2 = ⟨v,hv⟩ from Subtype.ext h2, he]
    · rw [show a1 = ⟨v,hv⟩ from Subtype.ext h1, show a2 = ⟨u,hu⟩ from Subtype.ext h2, he]
    · rw [show a1 = a2 from Subtype.ext (h1.trans h2.symm)]
  have huK : u ∈ K.verts := by
    by_contra hu
    apply hc12
    rw [← ha1, ← ha2]
    have h1 : a1.1 = v := hb1.resolve_left fun h => hu (Eq.subst (motive := fun t => t ∈ K.verts) h a1.2)
    have h2 : a2.1 = v := hb2.resolve_left fun h => hu (Eq.subst (motive := fun t => t ∈ K.verts) h a2.2)
    rw [show a1 = a2 from Subtype.ext (h1.trans h2.symm)]
  have hvK : v ∈ K.verts := by
    by_contra hv
    apply hc12
    rw [← ha1, ← ha2]
    have h1 : a1.1 = u := hb1.resolve_right fun h => hv (Eq.subst (motive := fun t => t ∈ K.verts) h a1.2)
    have h2 : a2.1 = u := hb2.resolve_right fun h => hv (Eq.subst (motive := fun t => t ∈ K.verts) h a2.2)
    rw [show a1 = a2 from Subtype.ext (h1.trans h2.symm)]
  set Cu := H.connectedComponentMk ⟨u,huK⟩ with hCu
  set Cv := H.connectedComponentMk ⟨v,hvK⟩ with hCv
  have hneq : Cu ≠ Cv := fun h => hdist huK hvK h
  -- the shores
  let S : Finset V := Finset.univ.filter (· ∈ S₀)
  let X : Finset V := Finset.univ.filter (fun a => ∃ h : a ∈ K.verts, H.connectedComponentMk ⟨a,h⟩ = Cu)
  let Y : Finset V := Finset.univ.filter (fun a => ∃ h : a ∈ K.verts, H.connectedComponentMk ⟨a,h⟩ = Cv)
  let U : Finset V := Finset.univ.filter (fun a => a ∉ S₀ ∧ a ∉ X ∧ a ∉ Y)
  have hmS : ∀ a, a ∈ S ↔ a ∈ S₀ := by intro a; simp [S]
  have hmX : ∀ a, a ∈ X ↔ ∃ h : a ∈ K.verts, H.connectedComponentMk ⟨a,h⟩ = Cu := by
    intro a; simp [X]
  have hmY : ∀ a, a ∈ Y ↔ ∃ h : a ∈ K.verts, H.connectedComponentMk ⟨a,h⟩ = Cv := by
    intro a; simp [Y]
  have hmU : ∀ a, a ∈ U ↔ a ∉ S₀ ∧ a ∉ X ∧ a ∉ Y := by intro a; simp [U]
  have huX : u ∈ X := (hmX u).mpr ⟨huK, rfl⟩
  have hvY : v ∈ Y := (hmY v).mpr ⟨hvK, rfl⟩
  have hXY : ∀ a, a ∈ X → a ∈ Y → False := by
    intro a hX hY
    obtain ⟨h1, e1⟩ := (hmX a).mp hX
    obtain ⟨h2, e2⟩ := (hmY a).mp hY
    exact hneq (e1.symm.trans e2)
  have hSX : ∀ a, a ∈ S → a ∈ X → False := by
    intro a hS hX
    obtain ⟨h1, -⟩ := (hmX a).mp hX
    exact (hKmem a).mp h1 ((hmS a).mp hS)
  have hSY : ∀ a, a ∈ S → a ∈ Y → False := by
    intro a hS hY
    obtain ⟨h1, -⟩ := (hmY a).mp hY
    exact (hKmem a).mp h1 ((hmS a).mp hS)
  -- edges leaving X or Y
  have hne_uv : ∀ a b : V, a ≠ u → a ≠ v → s(a,b) ≠ s(u,v) := by
    intro a b hau hav he
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hau h1
    · exact hav h1
  have hclosed : ∀ a b : K.verts, H.Adj a b → H.connectedComponentMk a = H.connectedComponentMk b :=
    fun a b h => SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h
  have hUclosed : ∀ a m : K.verts, a.1 ∈ U → H.Adj a m → m.1 ∈ U := by
    intro a m ha hadj
    obtain ⟨haS, haX, haY⟩ := (hmU a.1).mp ha
    refine (hmU m.1).mpr ⟨(hKmem m.1).mp m.2, ?_, ?_⟩
    · intro hmX'
      obtain ⟨h1, e1⟩ := (hmX m.1).mp hmX'
      exact haX ((hmX a.1).mpr ⟨a.2, (hclosed a m hadj).trans e1⟩)
    · intro hmY'
      obtain ⟨h1, e1⟩ := (hmY m.1).mp hmY'
      exact haY ((hmY a.1).mpr ⟨a.2, (hclosed a m hadj).trans e1⟩)
  have hUu : ∀ a, a ∈ U → a ≠ u ∧ a ≠ v := by
    intro a ha
    obtain ⟨-, haX, haY⟩ := (hmU a).mp ha
    exact ⟨fun h => haX (h ▸ huX), fun h => haY (h ▸ hvY)⟩
  -- transfer of reachability between H and G[U]
  let GU := G.induce {a | a ∈ U}
  have hUK : ∀ a, a ∈ U → a ∈ K.verts := fun a ha => (hKmem a).mpr ((hmU a).mp ha).1
  let φ : GU →g H :=
    { toFun := fun b => ⟨b.1, hUK b.1 b.2⟩
      map_rel' := by
        intro b1 b2 h
        apply hHadj
        exact hG'adj _ _ (hne_uv _ _ (hUu _ b1.2).1 (hUu _ b1.2).2) h }
  have hwalk : ∀ (a b : K.verts) (p : H.Walk a b) (ha : a.1 ∈ U),
      ∃ hb : b.1 ∈ U, GU.Reachable ⟨a.1, ha⟩ ⟨b.1, hb⟩ := by
    intro a b p
    induction p with
    | nil => intro ha; exact ⟨ha, SimpleGraph.Reachable.refl _⟩
    | cons hadj p ih =>
      intro ha
      rename_i a' m b'
      have hm := hUclosed a' m ha hadj
      obtain ⟨hb, hr⟩ := ih hm
      refine ⟨hb, SimpleGraph.Reachable.trans ?_ hr⟩
      exact SimpleGraph.Adj.reachable (by simpa [GU] using hHadj' _ _ hadj)
  -- odd components of G[U]
  have hrepU : ∀ c ∈ H.oddComponents \ Bset, ∀ a ∈ c.supp, a.1 ∈ U := by
    intro c hc a ha
    refine (hmU a.1).mpr ⟨(hKmem a.1).mp a.2, ?_, ?_⟩
    · intro hX
      obtain ⟨h1, e1⟩ := (hmX a.1).mp hX
      apply hc.2
      refine ⟨⟨u,huK⟩, ?_, Or.inl rfl⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha ⊢
      rw [← ha]
      exact e1.symm
    · intro hY
      obtain ⟨h1, e1⟩ := (hmY a.1).mp hY
      apply hc.2
      refine ⟨⟨v,hvK⟩, ?_, Or.inr rfl⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha ⊢
      rw [← ha]
      exact e1.symm
  let rep : H.ConnectedComponent → K.verts := fun c => c.nonempty_supp.some
  have hrep : ∀ c, rep c ∈ c.supp := fun c => c.nonempty_supp.some_mem
  have hsupp : ∀ c (hc : c ∈ H.oddComponents \ Bset),
      Subtype.val '' (GU.connectedComponentMk ⟨(rep c).1, hrepU c hc _ (hrep c)⟩).supp =
        Subtype.val '' c.supp := by
    intro c hc
    ext a
    simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨φ b, ?_, rfl⟩
      have hr : GU.Reachable ⟨(rep c).1, _⟩ b := SimpleGraph.ConnectedComponent.exact hb.symm
      have := hr.map φ
      have hrc := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hrep c)
      rw [← hrc]
      exact (SimpleGraph.ConnectedComponent.sound this).symm
    · rintro ⟨b, hb, rfl⟩
      have hrc := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hrep c)
      have hr : H.Reachable (rep c) b := SimpleGraph.ConnectedComponent.exact (hrc.trans hb.symm)
      obtain ⟨p⟩ := hr
      obtain ⟨hbU, hr'⟩ := hwalk _ _ p (hrepU c hc _ (hrep c))
      exact ⟨⟨b.1, hbU⟩, (SimpleGraph.ConnectedComponent.sound hr').symm, rfl⟩
  let gs : ↥(H.oddComponents \ Bset) → ↥GU.oddComponents := fun c =>
    ⟨GU.connectedComponentMk ⟨(rep c.1).1, hrepU c.1 c.2 _ (hrep c.1)⟩, by
      have h1 := Set.ncard_image_of_injective
        (GU.connectedComponentMk ⟨(rep c.1).1, hrepU c.1 c.2 _ (hrep c.1)⟩).supp
        Subtype.val_injective
      have h2 := Set.ncard_image_of_injective c.1.supp Subtype.val_injective
      rw [hsupp c.1 c.2] at h1
      show Odd _
      rw [← h1, h2]
      exact c.2.1⟩
  have hgs : Function.Injective gs := by
    rintro ⟨c1, hc1⟩ ⟨c2, hc2⟩ he
    simp only [gs, Subtype.mk.injEq] at he
    have hr := (SimpleGraph.ConnectedComponent.exact he).map φ
    have h1 := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hrep c1)
    have h2 := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hrep c2)
    apply Subtype.ext
    show c1 = c2
    rw [← h1, ← h2]
    exact SimpleGraph.ConnectedComponent.sound hr
  have hUodd : (H.oddComponents \ Bset).ncard ≤ GU.oddComponents.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective gs hgs
  have hSc : S.card = S₀.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [S]
  have hBle : (H.oddComponents ∩ Bset).ncard ≤ 2 := by
    have hsub : H.oddComponents ∩ Bset ⊆ {Cu, Cv} := by
      rintro c ⟨-, a, ha, hb⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha
      rcases hb with h | h
      · left; rw [← ha, show a = ⟨u,huK⟩ from Subtype.ext h]
      · right; rw [← ha, show a = ⟨v,hvK⟩ from Subtype.ext h]; rfl
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair hneq).le
  -- S nonempty
  have hSne : S.Nonempty := by
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have hS0 : ∀ a, a ∉ S₀ := fun a ha => by
      have : a ∈ S := (hmS a).mpr ha
      rw [hS] at this
      exact absurd this (Finset.notMem_empty a)
    let ψ : (G.deleteEdges {s(u,v)}) →g H :=
      { toFun := fun a => ⟨a, (hKmem a).mpr (hS0 a)⟩
        map_rel' := by intro a b h; exact hHadj _ _ h }
    exact hneq (SimpleGraph.ConnectedComponent.sound (hpath.map ψ))
  refine ⟨S, X, Y, U, hSne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, huX, hvY, ?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun a h1 h2 => hSX a h1 h2
  · exact Finset.disjoint_left.mpr fun a h1 h2 => hSY a h1 h2
  · exact Finset.disjoint_left.mpr fun a h1 h2 => ((hmU a).mp h2).1 ((hmS a).mp h1)
  · exact Finset.disjoint_left.mpr fun a h1 h2 => hXY a h1 h2
  · exact Finset.disjoint_left.mpr fun a h1 h2 => ((hmU a).mp h2).2.1 h1
  · exact Finset.disjoint_left.mpr fun a h1 h2 => ((hmU a).mp h2).2.2 h1
  · rw [Finset.eq_univ_iff_forall]
    intro a
    simp only [Finset.mem_union]
    by_cases h1 : a ∈ S₀
    · exact Or.inl (Or.inl (Or.inl ((hmS a).mpr h1)))
    · by_cases h2 : a ∈ X
      · exact Or.inl (Or.inl (Or.inr h2))
      · by_cases h3 : a ∈ Y
        · exact Or.inl (Or.inr h3)
        · exact Or.inr ((hmU a).mpr ⟨h1, h2, h3⟩)
  · intro a ha b hb hab
    obtain ⟨h1, e1⟩ := (hmX a).mp ha
    obtain ⟨h2, e2⟩ := (hmY b).mp hb
    by_cases he : s(a,b) = s(u,v)
    · rcases Sym2.eq_iff.mp he with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact ⟨h3, h4⟩
      · exfalso
        exact hXY v (h3 ▸ ha) hvY
    · exfalso
      have hH := hHadj ⟨a,h1⟩ ⟨b,h2⟩ (hG'adj _ _ he hab)
      exact hneq (e1.symm.trans ((hclosed _ _ hH).trans e2))
  · intro w hw z hz hwz
    obtain ⟨hwS, hwX, hwY⟩ := (hmU w).mp hw
    obtain ⟨hwu, hwv⟩ := hUu w hw
    have hH := hHadj ⟨w, hUK w hw⟩ ⟨z, ?_⟩ (hG'adj _ _ (hne_uv _ _ hwu hwv) hwz)
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨h1, e1⟩ := (hmX z).mp hz
        exact hwX ((hmX w).mpr ⟨hUK w hw, (hclosed _ _ hH).trans e1⟩)
      · obtain ⟨h1, e1⟩ := (hmY z).mp hz
        exact hwY ((hmY w).mpr ⟨hUK w hw, (hclosed _ _ hH).trans e1⟩)
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact ((hmX z).mp hz).1
      · exact ((hmY z).mp hz).1
  · have h1 : S₀.ncard ≤ (H.oddComponents \ Bset).ncard := by omega
    rw [hSc]
    exact h1.trans hUodd
