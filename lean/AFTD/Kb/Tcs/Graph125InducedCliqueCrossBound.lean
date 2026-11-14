import AFTD.Prelude
import AFTD.Kb.Tcs.GraphCliquePartitionOrientedCrossDegreeBound

/-!
# graph_125_induced_clique_cross_bound

Topic: graphs   Node: 833c5ca6dfa7

Provenance: helper lemma. Induced-graph crossing bound for the OP-110 exceptional-vertex reduction.

If the 124 vertices outside a distinguished vertex of a graph form three color classes that are cliques, then the number of crossing arcs of any oriented spanning subdigraph among those vertices plus 2501 is at most the graph edge count minus the distinguished vertex degree.
-/

set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
private lemma in833_size124 (a b c x e : ℕ) (hs : a+b+c=124)
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

theorem graph_125_induced_clique_cross_bound
    (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj]
    (D : Digraph (Fin 125)) [DecidableRel D.Adj] (x : Fin 125) (col : Fin 125 → Fin 3)
    (hclique : ∀ u v, u ≠ x → v ≠ x → col u = col v → u ≠ v → G.Adj u v)
    (hsub : ∀ u v, D.Adj u v → G.Adj u v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u) :
    let S : Set (Fin 125) := {x}ᶜ
    let H := G.induce S
    let E : Digraph S := ⟨fun u v => D.Adj u.1 v.1⟩
    (∑ u : S, (Finset.univ.filter fun v : S => col v.1 ≠ col u.1 ∧ E.Adj u v).card) + 2501 ≤
      G.edgeFinset.card - G.degree x := by
  classical
  let S : Set (Fin 125) := {x}ᶜ
  let H := G.induce S
  let E : Digraph S := ⟨fun u v => D.Adj u.1 v.1⟩
  let color : S → Fin 3 := fun u => col u.1
  let n : Fin 3 → ℕ := fun i => (Finset.univ.filter fun v : S => color v = i).card
  let cross : ℕ := ∑ u : S, (Finset.univ.filter fun v : S => color v ≠ color u ∧ E.Adj u v).card
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
  have hsub' : ∀ u v : S, E.Adj u v → H.Adj u v := fun u v h => hsub u.1 v.1 h
  have hori' : ∀ u v : S, E.Adj u v → ¬ E.Adj v u := fun u v h => hori u.1 v.1 h
  have hbound := graph_clique_partition_oriented_cross_degree_bound S (Fin 3) H E color hc hsub' hori'
  change (∑ i : Fin 3, n i*(n i-1)) + 2*cross ≤ 2*H.edgeFinset.card at hbound
  have hre : (∑ i : Fin 3, n i*(n i-1)) =
      n 0*(n 0-1)+n 1*(n 1-1)+n 2*(n 2-1) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Nat.add_zero]
    omega
  rw [hre] at hbound
  have hbase := in833_size124 (n 0) (n 1) (n 2) cross H.edgeFinset.card hsizes hbound
  have hedges : H.edgeFinset.card = G.edgeFinset.card - G.degree x := by
    dsimp [H,S]
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton, SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  change cross + 2501 ≤ G.edgeFinset.card - G.degree x
  rw [← hedges]
  omega
