import AFTD.Prelude
import AFTD.Kb.Tcs.GraphCliquePartitionOrientedCrossDegreeBound

/-!
# graph_125_three_cliques_except_vertex_bounds

Topic: graphs   Node: 91538d6cb11c

Provenance: helper lemma. Clique-edge capacity after deleting one vertex in the OP-110 order-125 reduction.

If a graph on 125 vertices has at most 2583 edges and its vertices other than one distinguished vertex form three cliques, then at least 2501 graph edges avoid that vertex and each clique has at least seven vertices.
-/

set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
private lemma in833_exsz_bound124_7f3 (a b c x e : ℕ) (hs : a+b+c=124)
    (hbound : a*(a-1)+b*(b-1)+c*(c-1)+2*x ≤ 2*e) : 2501+x ≤ e := by
  have hprod (n : ℕ) : n*(n-1)+n=n*n := by
    cases n with
    | zero => simp
    | succ n => simp; ring
  have ha := hprod a
  have hb := hprod b
  have hc := hprod c
  have he : a*a+b*b+c*c+2*x ≤ 2*e+124 := by nlinarith
  have hs' : (a:ℤ)+b+c=124 := by exact_mod_cast hs
  have he' : (a:ℤ)*a+b*b+c*c+2*x ≤ 2*e+124 := by exact_mod_cast he
  have h1 : (0:ℤ) ≤ ((a:ℤ)-b)^2 := sq_nonneg _
  have h2 : (0:ℤ) ≤ ((a:ℤ)-c)^2 := sq_nonneg _
  have h3 : (0:ℤ) ≤ ((b:ℤ)-c)^2 := sq_nonneg _
  have out : (2501:ℤ)+x ≤ e := by nlinarith
  exact_mod_cast out


private lemma in833_exsz_arith124_7f3 (a b c x : ℕ) (hs : a + b + c = 124)
    (h : a * (a - 1) + b * (b - 1) + c * (c - 1) + 2*x ≤ 5166) :
    7 ≤ a ∧ 7 ≤ b ∧ 7 ≤ c ∧ x ≤ 82 := by
  have hprod (n : ℕ) : n * (n - 1) + n = n*n := by
    cases n with
    | zero => simp
    | succ n => simp; ring
  have ha := hprod a
  have hb := hprod b
  have hc := hprod c
  have hsum : a*a + b*b + c*c + 2*x ≤ 5290 := by nlinarith
  have hx : x ≤ 82 := by
    have h1 : (0:ℤ) ≤ ((a:ℤ) - b)^2 := sq_nonneg _
    have h2 : (0:ℤ) ≤ ((b:ℤ) - c)^2 := sq_nonneg _
    have h3 : (0:ℤ) ≤ ((a:ℤ) - c)^2 := sq_nonneg _
    have hs' : (a:ℤ) + b + c = 124 := by exact_mod_cast hs
    have hh' : (a:ℤ)*a + b*b + c*c + 2*x ≤ 5290 := by exact_mod_cast hsum
    have out : (x:ℤ) ≤ 82 := by nlinarith
    exact_mod_cast out
  have hsize (p q r : ℕ) (hs : p+q+r=124)
      (hh : p*p + q*q + r*r ≤ 5290) : 7 ≤ p := by
    by_contra hp
    have hp' : p ≤ 6 := by omega
    have hs' : (p:ℤ) + q + r = 124 := by exact_mod_cast hs
    have hh' : (p:ℤ)*p + q*q + r*r ≤ 5290 := by exact_mod_cast hh
    have hp'' : (p:ℤ) ≤ 6 := by exact_mod_cast hp'
    have hn : (0:ℤ) ≤ p := by exact_mod_cast Nat.zero_le p
    have hq : (0:ℤ) ≤ q := by exact_mod_cast Nat.zero_le q
    have hr : (0:ℤ) ≤ r := by exact_mod_cast Nat.zero_le r
    have hdiff : (0:ℤ) ≤ ((q:ℤ)-(r:ℤ))^2 := sq_nonneg _
    have hbig : (0:ℤ) ≤ ((q:ℤ)+(r:ℤ)-118) * ((q:ℤ)+(r:ℤ)+118) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (p:ℤ)]
  have hh : a*a+b*b+c*c ≤ 5290 := by omega
  refine ⟨hsize a b c hs hh, ?_, ?_, hx⟩
  · apply hsize b a c <;> omega
  · apply hsize c a b <;> omega

theorem graph_125_three_cliques_except_vertex_bounds
    (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj] (x : Fin 125) (col : Fin 125 → Fin 3)
    (hclique : ∀ u v, u ≠ x → v ≠ x → col u = col v → u ≠ v → G.Adj u v)
    (hedges : G.edgeFinset.card ≤ 2583) :
    G.degree x + 2501 ≤ G.edgeFinset.card ∧
    (∀ i, 7 ≤ (Finset.univ.filter fun v => v ≠ x ∧ col v = i).card) := by
  classical
  let S : Set (Fin 125) := {x}ᶜ
  let H := G.induce S
  let E : Digraph S := ⟨fun _ _ => False⟩
  let color : S → Fin 3 := fun u => col u.1
  let n : Fin 3 → ℕ := fun i => (Finset.univ.filter fun v : S => color v = i).card
  have hcard : Fintype.card S = 124 := by
    dsimp [S]
    rw [Fintype.card_compl_set]
    simp
  have hsizes : n 0+n 1+n 2=124 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := color) (s := (Finset.univ : Finset S))
      (t := (Finset.univ : Finset (Fin 3))) (by simp)
    simp only [Finset.card_univ, hcard, Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero] at h
    change 124 = n 0+(n 1+n 2) at h
    omega
  have hc : ∀ u v : S, color u = color v → u ≠ v → H.Adj u v := by
    intro u v hcolor hne
    have hu : u.1 ≠ x := by
      have hp : u.1 ∈ ({x}ᶜ : Set (Fin 125)) := u.2
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
    have hv : v.1 ≠ x := by
      have hp : v.1 ∈ ({x}ᶜ : Set (Fin 125)) := v.2
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
    have huv : u.1 ≠ v.1 := fun h => hne (Subtype.ext h)
    exact hclique u.1 v.1 hu hv hcolor huv
  have hsub : ∀ u v : S, E.Adj u v → H.Adj u v := by intros u v h; exact h.elim
  have hori : ∀ u v : S, E.Adj u v → ¬ E.Adj v u := by intros u v h; exact h.elim
  have hbound := graph_clique_partition_oriented_cross_degree_bound S (Fin 3) H E color hc hsub hori
  have hbound0 : (∑ i : Fin 3, n i * (n i - 1)) ≤ 2 * H.edgeFinset.card := by
    simpa [E,n,color] using hbound
  have hre : (∑ i : Fin 3, n i * (n i - 1)) =
      n 0*(n 0-1)+n 1*(n 1-1)+n 2*(n 2-1) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Nat.add_zero]
    omega
  rw [hre] at hbound0
  have hcount : H.edgeFinset.card = G.edgeFinset.card - G.degree x := by
    dsimp [H,S]
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton, SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have hbase := in833_exsz_bound124_7f3 (n 0) (n 1) (n 2) 0 H.edgeFinset.card hsizes (by omega)
  have hnum : n 0*(n 0-1)+n 1*(n 1-1)+n 2*(n 2-1)+2*0 ≤ 5166 := by omega
  have hsize := in833_exsz_arith124_7f3 (n 0) (n 1) (n 2) 0 hsizes hnum
  have hconvert (i : Fin 3) : n i =
      (Finset.univ.filter fun v => v ≠ x ∧ col v = i).card := by
    dsimp [n]
    refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
    · intro v hv
      have hvx : v.1 ≠ x := by
        have hp : v.1 ∈ ({x}ᶜ : Set (Fin 125)) := v.2
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨hvx,hv⟩
    · intro u hu v hv huv
      exact Subtype.ext huv
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hvS : v ∈ S := by
        change v ∈ ({x}ᶜ : Set (Fin 125))
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hv.1
      refine ⟨⟨v,hvS⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hv.2
  constructor
  · omega
  · intro i
    rw [← hconvert]
    fin_cases i
    · exact hsize.1
    · exact hsize.2.1
    · exact hsize.2.2.1
