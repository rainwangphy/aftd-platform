import AFTD.Prelude

/-!
# graph_126_three_clique_partition_oriented_cross_bound

Topic: graphs   Node: 34b867f2a892

Provenance: helper lemma. Edge-counting step for the order-126 reduction for OP-110.

For a graph on 126 vertices partitioned into three cliques, with at most 2604 graph edges, each part has at least seven vertices and every oriented subdigraph has at most 21 arcs between the parts.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
private lemma in833_arith (a b c x : ℕ) (hs : a + b + c = 126)
    (h : a * (a - 1) + b * (b - 1) + c * (c - 1) + 2*x ≤ 5208) :
    7 ≤ a ∧ 7 ≤ b ∧ 7 ≤ c ∧ x ≤ 21 := by
  have hprod (n : ℕ) : n * (n - 1) + n = n*n := by
    cases n with
    | zero => simp
    | succ n => simp; ring
  have ha := hprod a
  have hb := hprod b
  have hc := hprod c
  have hsum : a*a + b*b + c*c + 2*x ≤ 5334 := by nlinarith
  have hx : x ≤ 21 := by
    have h1 : (0:ℤ) ≤ ((a:ℤ) - b)^2 := sq_nonneg _
    have h2 : (0:ℤ) ≤ ((b:ℤ) - c)^2 := sq_nonneg _
    have h3 : (0:ℤ) ≤ ((a:ℤ) - c)^2 := sq_nonneg _
    have hs' : (a:ℤ) + b + c = 126 := by exact_mod_cast hs
    have hh' : (a:ℤ)*a + b*b + c*c + 2*x ≤ 5334 := by exact_mod_cast hsum
    have out : (x:ℤ) ≤ 21 := by nlinarith
    exact_mod_cast out
  have hsize (p q r : ℕ) (hs : p+q+r=126)
      (hh : p*p + q*q + r*r ≤ 5334) : 7 ≤ p := by
    by_contra hp
    have hp' : p ≤ 6 := by omega
    have hs' : (p:ℤ) + q + r = 126 := by exact_mod_cast hs
    have hh' : (p:ℤ)*p + q*q + r*r ≤ 5334 := by exact_mod_cast hh
    have hp'' : (p:ℤ) ≤ 6 := by exact_mod_cast hp'
    have hn : (0:ℤ) ≤ p := by exact_mod_cast Nat.zero_le p
    have hq : (0:ℤ) ≤ q := by exact_mod_cast Nat.zero_le q
    have hr : (0:ℤ) ≤ r := by exact_mod_cast Nat.zero_le r
    have hdiff : (0:ℤ) ≤ ((q:ℤ)-(r:ℤ))^2 := sq_nonneg _
    have hbig : (0:ℤ) ≤ ((q:ℤ)+(r:ℤ)-120) * ((q:ℤ)+(r:ℤ)+120) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (p:ℤ)]
  have hh : a*a+b*b+c*c ≤ 5334 := by omega
  refine ⟨hsize a b c hs hh, ?_, ?_, hx⟩
  · apply hsize b a c <;> omega
  · apply hsize c a b <;> omega

theorem graph_126_three_clique_partition_oriented_cross_bound
    (G : SimpleGraph (Fin 126)) [DecidableRel G.Adj]
    (D : Digraph (Fin 126)) [DecidableRel D.Adj] (col : Fin 126 → Fin 3)
    (hclique : ∀ u v, col u = col v → u ≠ v → G.Adj u v)
    (hsub : ∀ u v, D.Adj u v → G.Adj u v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hedges : G.edgeFinset.card ≤ 2604) :
    (∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card) ∧
    (∑ v : Fin 126, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card) ≤ 21 := by
  classical
  let S : Fin 3 → Finset (Fin 126) := fun i => Finset.univ.filter fun v => col v = i
  let n : Fin 3 → ℕ := fun i => (S i).card
  let inside : Fin 126 → Finset (Fin 126) := fun v => (S (col v)).erase v
  let out : Fin 126 → Finset (Fin 126) := fun v =>
    Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w
  let inc : Fin 126 → Finset (Fin 126) := fun v =>
    Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj w v
  have hlocal (v : Fin 126) : (inside v).card + (out v).card + (inc v).card ≤ G.degree v := by
    have hab : Disjoint (inside v) (out v) := by
      apply Finset.disjoint_left.mpr
      intro w hw1 hw2
      have h1 : col w = col v := (Finset.mem_filter.mp (Finset.mem_erase.mp hw1).2).2
      have h2 : col w ≠ col v := (Finset.mem_filter.mp hw2).2.1
      exact h2 h1
    have hac : Disjoint (inside v) (inc v) := by
      apply Finset.disjoint_left.mpr
      intro w hw1 hw2
      have h1 : col w = col v := (Finset.mem_filter.mp (Finset.mem_erase.mp hw1).2).2
      have h2 : col w ≠ col v := (Finset.mem_filter.mp hw2).2.1
      exact h2 h1
    have hbc : Disjoint (out v) (inc v) := by
      apply Finset.disjoint_left.mpr
      intro w hw1 hw2
      have h1 : D.Adj v w := (Finset.mem_filter.mp hw1).2.2
      have h2 : D.Adj w v := (Finset.mem_filter.mp hw2).2.2
      exact hori v w h1 h2
    have hall : Disjoint (inside v) (out v ∪ inc v) := Finset.disjoint_union_right.mpr ⟨hab, hac⟩
    have hsubset : inside v ∪ (out v ∪ inc v) ⊆ G.neighborFinset v := by
      intro w hw
      simp only [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_union.mp hw with ha | ha
      · have hw' := Finset.mem_erase.mp ha
        have hc : col w = col v := (Finset.mem_filter.mp hw'.2).2
        exact hclique v w hc.symm hw'.1.symm
      · rcases Finset.mem_union.mp ha with hb | hc
        · exact hsub v w (Finset.mem_filter.mp hb).2.2
        · exact (hsub w v (Finset.mem_filter.mp hc).2.2).symm
    have hh := Finset.card_le_card hsubset
    rw [Finset.card_union_of_disjoint hall, Finset.card_union_of_disjoint hbc] at hh
    change _ ≤ G.degree v at hh
    omega
  have hcount (v : Fin 126) : (inside v).card = n (col v) - 1 := by
    apply Finset.card_erase_of_mem
    simp [S]
  have hsizes : n 0 + n 1 + n 2 = 126 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := col) (s := (Finset.univ : Finset (Fin 126)))
        (t := (Finset.univ : Finset (Fin 3))) (by simp)
    simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Nat.add_zero] at h
    change 126 = n 0 + (n 1 + n 2) at h
    omega
  have hinside : (∑ v : Fin 126, (inside v).card) = ∑ i : Fin 3, n i * (n i - 1) := by
    simp_rw [hcount]
    rw [← Finset.sum_fiberwise Finset.univ col]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ v ∈ Finset.univ.filter (fun v => col v = i), (n (col v) - 1)) =
          ∑ _v ∈ Finset.univ.filter (fun v => col v = i), (n i - 1) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [(Finset.mem_filter.mp hv).2]
      _ = n i * (n i - 1) := by simp [n,S]
  have hcross : (∑ v : Fin 126, (out v).card) = ∑ v : Fin 126, (inc v).card := by
    simp only [out, inc, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : col w = col v <;> by_cases hd : D.Adj v w <;> simp [h, Ne.symm, hd]
  have hsum : (∑ i : Fin 3, n i * (n i - 1)) + 2 * (∑ v : Fin 126, (out v).card) ≤ 5208 := by
    have hh := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin 126))) => hlocal v)
    simp only [Finset.sum_add_distrib] at hh
    rw [hinside, ← hcross, G.sum_degrees_eq_twice_card_edges] at hh
    omega
  have hre : (∑ i : Fin 3, n i * (n i - 1)) =
      n 0 * (n 0 - 1) + n 1 * (n 1 - 1) + n 2 * (n 2 - 1) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Nat.add_zero]
    omega
  have hs : n 0 * (n 0 - 1) + n 1 * (n 1 - 1) + n 2 * (n 2 - 1) +
      2 * (∑ v : Fin 126, (out v).card) ≤ 5208 := by
    rw [hre] at hsum
    exact hsum
  have h := in833_arith (n 0) (n 1) (n 2) _ hsizes hs
  constructor
  · intro i
    change 7 ≤ n i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
  · exact h.2.2.2
