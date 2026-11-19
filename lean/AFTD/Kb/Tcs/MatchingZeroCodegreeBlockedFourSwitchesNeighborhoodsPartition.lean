import AFTD.Prelude

/-!
# matching_zero_codegree_blocked_four_switches_neighborhoods_partition

Topic: graphs   Node: f437856e954b

Provenance: helper lemma. OP-1957: blocked four-switch partition of the residual graph; experiment 34747 tests small finite orders.

If uv is a perfect-matching edge with no common complement neighbor and no four-switch, every other vertex lies in exactly one endpoint complement neighborhood.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

private theorem in1047_partition_tuple4_injective {V : Type*} (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [rfl, absurd hij hab, absurd hij hac, absurd hij had,
    absurd hij hab.symm, rfl, absurd hij hbc, absurd hij hbd,
    absurd hij hac.symm, absurd hij hbc.symm, rfl, absurd hij hcd,
    absurd hij had.symm, absurd hij hbd.symm, absurd hij hcd.symm, rfl]

theorem matching_zero_codegree_blocked_four_switches_neighborhoods_partition
    {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v : V) (huv : P.Adj u v)
    (hfar2 : ∀ x : V, ¬ ((Gᶜ).Adj u x ∧ (Gᶜ).Adj v x))
    (h4 : ¬ ∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → V) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b) :
    ∀ x, x ≠ u → x ≠ v → (Gᶜ).Adj u x ∨ (Gᶜ).Adj v x := by
  classical
  intro x hxu hxv
  by_contra hnone
  have hUX : ¬ (Gᶜ).Adj u x := fun h => hnone (Or.inl h)
  have hVX : ¬ (Gᶜ).Adj v x := fun h => hnone (Or.inr h)
  have hux : G.Adj u x := by
    by_contra h
    exact hUX ((SimpleGraph.compl_adj G u x).2 ⟨hxu.symm,h⟩)
  have hvx : G.Adj v x := by
    by_contra h
    exact hVX ((SimpleGraph.compl_adj G v x).2 ⟨hxv.symm,h⟩)
  have hmate : ∀ {a b c : V}, P.Adj a b → P.Adj a c → b = c :=
    fun {a b c} h1 h2 => (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP a).unique h1 h2
  have huvne : u ≠ v := (P.adj_sub huv).ne
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
  have hUy : ¬ G.Adj u y := by
    intro h
    apply h4
    refine ⟨x,y,?_,hxy,hvx,h⟩
    exact in1047_partition_tuple4_injective u v x y huvne hxu.symm hyu.symm hxv.symm hyv.symm hxyne
  have hVy : ¬ G.Adj v y := by
    intro h
    apply h4
    refine ⟨y,x,?_,hxy.symm,h,hux⟩
    exact in1047_partition_tuple4_injective u v y x huvne hyu.symm hxu.symm hyv.symm hxv.symm hxyne.symm
  exact hfar2 y ⟨(SimpleGraph.compl_adj G u y).2 ⟨hyu.symm,hUy⟩,
    (SimpleGraph.compl_adj G v y).2 ⟨hyv.symm,hVy⟩⟩
