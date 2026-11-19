import AFTD.Prelude

/-!
# matching_zero_codegree_blocked_switches_neighborhoods_complete

Topic: graphs   Node: 62b141599355

Provenance: helper lemma. OP-1957: complete cross-neighborhood strengthening of the four-cycle switch lemma; experiment 34746 checks residual orders six through twelve.

If uv is a perfect-matching edge with no common complement neighbor, and four- and six-switches at uv are blocked, every complement neighbor of u is adjacent in the complement to every complement neighbor of v.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

private theorem in1047_allcross_tuple4_injective {V : Type*} (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [rfl, absurd hij hab, absurd hij hac, absurd hij had,
    absurd hij hab.symm, rfl, absurd hij hbc, absurd hij hbd,
    absurd hij hac.symm, absurd hij hbc.symm, rfl, absurd hij hcd,
    absurd hij had.symm, absurd hij hbd.symm, absurd hij hcd.symm, rfl]

private theorem in1047_allcross_tuple6_injective {V : Type*} (a b c d e f : V)
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

theorem matching_zero_codegree_blocked_switches_neighborhoods_complete
    {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v : V) (huv : P.Adj u v)
    (hfar2 : ∀ x : V, ¬ ((Gᶜ).Adj u x ∧ (Gᶜ).Adj v x))
    (h4 : ¬ ∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → V) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b)
    (h6 : ¬ ∃ a b c d, Function.Injective (![u,v,a,b,c,d] : Fin 6 → V) ∧ P.Adj a b ∧ P.Adj c d ∧ G.Adj v b ∧ G.Adj a c ∧ G.Adj u d) :
    ∀ x z, (Gᶜ).Adj u x → (Gᶜ).Adj v z → (Gᶜ).Adj x z := by
  classical
  intro x z huxH hvzH
  have hmate : ∀ {a b c : V}, P.Adj a b → P.Adj a c → b = c :=
    fun {a b c} h1 h2 => (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP a).unique h1 h2
  have huvG : G.Adj u v := P.adj_sub huv
  have huvne : u ≠ v := huvG.ne
  have hxu : x ≠ u := huxH.ne.symm
  have hzv : z ≠ v := hvzH.ne.symm
  have huxx : ¬ G.Adj u x := (SimpleGraph.compl_adj G u x).1 huxH |>.2
  have hvz : ¬ G.Adj v z := (SimpleGraph.compl_adj G v z).1 hvzH |>.2
  have hxv : x ≠ v := by
    intro h
    subst x
    exact huxx huvG
  have hzu : z ≠ u := by
    intro h
    subst z
    exact hvz huvG.symm
  have hvx : G.Adj v x := by
    by_contra h
    exact hfar2 x ⟨huxH, (SimpleGraph.compl_adj G v x).2 ⟨hxv.symm,h⟩⟩
  have huz : G.Adj u z := by
    by_contra h
    exact hfar2 z ⟨(SimpleGraph.compl_adj G u z).2 ⟨hzu.symm,h⟩,hvzH⟩
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
    exact in1047_allcross_tuple4_injective u v x y huvne hxu.symm hyu.symm hxv.symm hyv.symm hxyne
  have hvy : G.Adj v y := by
    by_contra h
    exact hfar2 y ⟨(SimpleGraph.compl_adj G u y).2 ⟨hyu.symm,huxy⟩,
      (SimpleGraph.compl_adj G v y).2 ⟨hyv.symm,h⟩⟩
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
    exact in1047_allcross_tuple4_injective u v t z huvne htu.symm hzu.symm htv.symm hzv.symm hztne.symm
  have hut : G.Adj u t := by
    by_contra h
    exact hfar2 t ⟨(SimpleGraph.compl_adj G u t).2 ⟨htu.symm,h⟩,
      (SimpleGraph.compl_adj G v t).2 ⟨htv.symm,hvt⟩⟩
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
    exact in1047_allcross_tuple6_injective u v x y z t huvne hxu.symm hyu.symm hzu.symm htu.symm
      hxv.symm hyv.symm hzv.symm htv.symm hxyne hxz hxt hyz hyt hztne
  exact (SimpleGraph.compl_adj G x z).2 ⟨hxz,hxzH⟩
