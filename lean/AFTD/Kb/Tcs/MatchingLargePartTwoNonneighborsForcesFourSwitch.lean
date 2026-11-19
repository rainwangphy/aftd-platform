import AFTD.Prelude

/-!
# matching_large_part_two_nonneighbors_forces_four_switch

Topic: graphs   Node: 41dbe9ffde23

Provenance: helper lemma. OP-1957: general large-part form of the saturated residual-twin four-switch; experiment 34829 checks the five-part instance.

A perfect matching containing uv admits a four-switch when a large part A contains u, v sees all of A, u has an A-neighbor, and the five vertices outside A include v and two nonadjacent vertices missing all of A.
-/

private theorem in1047_largepart_tuple4_injective {V : Type*} (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  exacts [rfl, absurd hij hab, absurd hij hac, absurd hij had,
    absurd hij hab.symm, rfl, absurd hij hbc, absurd hij hbd,
    absurd hij hac.symm, absurd hij hbc.symm, rfl, absurd hij hcd,
    absurd hij had.symm, absurd hij hbd.symm, absurd hij hcd.symm, rfl]

theorem matching_large_part_two_nonneighbors_forces_four_switch
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (P : G.Subgraph)
    (hP : P.IsPerfectMatching) (A : Finset V) (u v x y : V)
    (hu : u ∈ A) (hv : v ∉ A) (hx : x ∉ A) (hy : y ∉ A)
    (hcard : Fintype.card V = A.card+5) (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (huv : P.Adj u v) (hxyG : ¬ G.Adj x y)
    (hxA : ∀ a ∈ A, ¬ G.Adj x a) (hyA : ∀ a ∈ A, ¬ G.Adj y a)
    (hvA : ∀ a ∈ A, G.Adj v a) (huA : ∃ a ∈ A, G.Adj u a) :
    ∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → V) ∧
      P.Adj a b ∧ G.Adj v a ∧ G.Adj u b := by
  classical
  have hmate : ∀ {a b c : V}, P.Adj a b → P.Adj a c → b = c :=
    fun {a b c} h1 h2 => (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP a).unique h1 h2
  obtain ⟨p,hxp,_⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) x
  obtain ⟨q,hyq,_⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) y
  have hp : p ∉ A := fun h => hxA p h (P.adj_sub hxp)
  have hq : q ∉ A := fun h => hyA q h (P.adj_sub hyq)
  have hpx : p ≠ x := (P.adj_sub hxp).ne.symm
  have hqy : q ≠ y := (P.adj_sub hyq).ne.symm
  have hpy : p ≠ y := fun e => hxyG (e ▸ P.adj_sub hxp)
  have hqx : q ≠ x := fun e => hxyG ((e ▸ P.adj_sub hyq).symm)
  have hpv : p ≠ v := by
    intro e
    subst p
    have h : x = u := hmate hxp.symm huv.symm
    exact hx (h ▸ hu)
  have hqv : q ≠ v := by
    intro e
    subst q
    have h : y = u := hmate hyq.symm huv.symm
    exact hy (h ▸ hu)
  have hpq : p ≠ q := by
    intro e
    subst q
    exact hxy (hmate hxp.symm hyq.symm)
  let C : Finset V := Finset.univ \ A
  have hC : C.card = 5 := by
    dsimp [C]
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ]
    omega
  have hsub : ({v,x,y,p,q} : Finset V) ⊆ C := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [C, hv, hx, hy, hp, hq]
  have hfive : ({v,x,y,p,q} : Finset V).card = 5 := by
    simp [hxv, hyv, hxy, hpv, hpx, hpy, hqv, hqx, hqy, hpq,
      Ne.symm hxv, Ne.symm hyv, Ne.symm hxy, Ne.symm hpv, Ne.symm hpx,
      Ne.symm hpy, Ne.symm hqv, Ne.symm hqx, Ne.symm hqy, Ne.symm hpq]
  have hCeq : C = ({v,x,y,p,q} : Finset V) :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hC, hfive])).symm
  obtain ⟨b,hb,hub⟩ := huA
  have hbu : b ≠ u := hub.ne.symm
  obtain ⟨a,hba,_⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) b
  have hbaG := P.adj_sub hba
  have haba : a ≠ b := hbaG.ne.symm
  have hau : a ≠ u := by
    intro e
    subst a
    have h : b = v := hmate hba.symm huv
    exact hv (h ▸ hb)
  have haA : a ∈ A := by
    by_contra ha
    have haC : a ∈ C := by simp [C, ha]
    rw [hCeq] at haC
    simp only [Finset.mem_insert, Finset.mem_singleton] at haC
    rcases haC with e | e | e | e | e
    · subst a; have h : b = u := hmate hba.symm huv.symm; exact hbu h
    · subst a; exact hxA b hb hbaG.symm
    · subst a; exact hyA b hb hbaG.symm
    · subst a; have h : b = x := hmate hba.symm hxp.symm; exact hx (h ▸ hb)
    · subst a; have h : b = y := hmate hba.symm hyq.symm; exact hy (h ▸ hb)
  have huvne : u ≠ v := (P.adj_sub huv).ne
  have hav : a ≠ v := fun e => hv (e ▸ haA)
  have hbv : b ≠ v := fun e => hv (e ▸ hb)
  exact ⟨a,b,in1047_largepart_tuple4_injective u v a b huvne hau.symm hbu.symm
    hav.symm hbv.symm haba, hba.symm, hvA a haA, hub⟩
