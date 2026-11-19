import AFTD.Prelude

/-!
# matching_zero_codegree_blocked_switches_forces_complement_four_cycle

Topic: graphs   Node: ff571d3800fa

Provenance: helper lemma. OP-1957: the zero-codegree short-switch obstruction contains a four-cycle; experiment 34629.

If a perfect-matching edge uv has no common complement neighbor, each endpoint has at least two graph neighbors, and no four- or six-switch is available, the complement contains a four-cycle with two vertices in each endpoint neighborhood.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

private theorem in1047_fourcycle_tuple4_injective {V : Type*} (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [rfl, absurd hij hab, absurd hij hac, absurd hij had,
    absurd hij hab.symm, rfl, absurd hij hbc, absurd hij hbd,
    absurd hij hac.symm, absurd hij hbc.symm, rfl, absurd hij hcd,
    absurd hij had.symm, absurd hij hbd.symm, absurd hij hcd.symm, rfl]

private theorem in1047_fourcycle_tuple6_injective {V : Type*} (a b c d e f : V)
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

theorem matching_zero_codegree_blocked_switches_forces_complement_four_cycle
    {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v : V) (huv : P.Adj u v)
    (hdeg_u : ∃ x y : V, x ≠ y ∧ G.Adj u x ∧ G.Adj u y)
    (hdeg_v : ∃ x y : V, x ≠ y ∧ G.Adj v x ∧ G.Adj v y)
    (hfar2 : ∀ x : V, ¬ ((Gᶜ).Adj u x ∧ (Gᶜ).Adj v x))
    (h4 : ¬ ∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → V) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b)
    (h6 : ¬ ∃ a b c d, Function.Injective (![u,v,a,b,c,d] : Fin 6 → V) ∧ P.Adj a b ∧ P.Adj c d ∧ G.Adj v b ∧ G.Adj a c ∧ G.Adj u d) :
    ∃ a b c d, Function.Injective (![u,v,a,b,c,d] : Fin 6 → V) ∧
      (Gᶜ).Adj u a ∧ (Gᶜ).Adj u b ∧ (Gᶜ).Adj v c ∧ (Gᶜ).Adj v d ∧
      (Gᶜ).Adj a c ∧ (Gᶜ).Adj a d ∧ (Gᶜ).Adj b c ∧ (Gᶜ).Adj b d := by
  classical
  have hmate : ∀ {a b c : V}, P.Adj a b → P.Adj a c → b = c :=
    fun {a b c} h1 h2 => (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP a).unique h1 h2
  have huvG : G.Adj u v := P.adj_sub huv
  have huvne : u ≠ v := huvG.ne
  have choose_other (s t : V) (h : ∃ x y : V, x ≠ y ∧ G.Adj s x ∧ G.Adj s y) :
      ∃ z, z ≠ t ∧ G.Adj s z := by
    obtain ⟨x,y,hxy,hx,hy⟩ := h
    by_cases hxt : x = t
    · refine ⟨y, ?_, hy⟩
      intro hyt
      exact hxy (hxt.trans hyt.symm)
    · exact ⟨x,hxt,hx⟩
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
  obtain ⟨x,hxu,hvx⟩ := choose_other v u hdeg_v
  have hxv : x ≠ v := hvx.symm.ne
  obtain ⟨y,hxy,_⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) x
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
    refine ⟨x,y,?_,hxy,hvx,h⟩
    exact in1047_fourcycle_tuple4_injective u v x y huvne hxu.symm hyu.symm hxv.symm hyv.symm hxyne
  have hvy : G.Adj v y := hnu y hyu hyv huxy
  have huxx : ¬ G.Adj u x := by
    intro h
    apply h4
    refine ⟨y,x,?_,hxy.symm,hvy,h⟩
    exact in1047_fourcycle_tuple4_injective u v y x huvne hyu.symm hxu.symm hyv.symm hxv.symm hxyne.symm
  obtain ⟨z,hzv,huz⟩ := choose_other u v hdeg_u
  have hzu : z ≠ u := huz.symm.ne
  obtain ⟨t,hzt,_⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) z
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
    refine ⟨t,z,?_,hzt.symm,h,huz⟩
    exact in1047_fourcycle_tuple4_injective u v t z huvne htu.symm hzu.symm htv.symm hzv.symm hztne.symm
  have hut : G.Adj u t := hnv t htu htv hvt
  have hvz : ¬ G.Adj v z := by
    intro h
    apply h4
    refine ⟨z,t,?_,hzt,h,hut⟩
    exact in1047_fourcycle_tuple4_injective u v z t huvne hzu.symm htu.symm hzv.symm htv.symm hztne
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
    refine ⟨x,y,z,t,?_,hxy,hzt,hvy,h,hut⟩
    exact in1047_fourcycle_tuple6_injective u v x y z t huvne hxu.symm hyu.symm hzu.symm htu.symm
      hxv.symm hyv.symm hzv.symm htv.symm hxyne hxz hxt hyz hyt hztne
  have hxtH : ¬ G.Adj x t := by
    intro h
    apply h6
    refine ⟨x,y,t,z,?_,hxy,hzt.symm,hvy,h,huz⟩
    exact in1047_fourcycle_tuple6_injective u v x y t z huvne hxu.symm hyu.symm htu.symm hzu.symm
      hxv.symm hyv.symm htv.symm hzv.symm hxyne hxt hxz hyt hyz hztne.symm
  have hyzH : ¬ G.Adj y z := by
    intro h
    apply h6
    refine ⟨y,x,z,t,?_,hxy.symm,hzt,hvx,h,hut⟩
    exact in1047_fourcycle_tuple6_injective u v y x z t huvne hyu.symm hxu.symm hzu.symm htu.symm
      hyv.symm hxv.symm hzv.symm htv.symm hxyne.symm hyz hyt hxz hxt hztne
  have hytH : ¬ G.Adj y t := by
    intro h
    apply h6
    refine ⟨y,x,t,z,?_,hxy.symm,hzt.symm,hvx,h,huz⟩
    exact in1047_fourcycle_tuple6_injective u v y x t z huvne hyu.symm hxu.symm htu.symm hzu.symm
      hyv.symm hxv.symm htv.symm hzv.symm hxyne.symm hyt hyz hxt hxz hztne.symm
  refine ⟨x,y,z,t,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact in1047_fourcycle_tuple6_injective u v x y z t huvne hxu.symm hyu.symm hzu.symm htu.symm
      hxv.symm hyv.symm hzv.symm htv.symm hxyne hxz hxt hyz hyt hztne
  · exact (SimpleGraph.compl_adj G u x).2 ⟨hxu.symm,huxx⟩
  · exact (SimpleGraph.compl_adj G u y).2 ⟨hyu.symm,huxy⟩
  · exact (SimpleGraph.compl_adj G v z).2 ⟨hzv.symm,hvz⟩
  · exact (SimpleGraph.compl_adj G v t).2 ⟨htv.symm,hvt⟩
  · exact (SimpleGraph.compl_adj G x z).2 ⟨hxz,hxzH⟩
  · exact (SimpleGraph.compl_adj G x t).2 ⟨hxt,hxtH⟩
  · exact (SimpleGraph.compl_adj G y z).2 ⟨hyz,hyzH⟩
  · exact (SimpleGraph.compl_adj G y t).2 ⟨hyt,hytH⟩
