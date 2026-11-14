import AFTD.Prelude
import AFTD.Kb.Tcs.GraphCliquePartitionOrientedCrossDegreeBound

/-!
# graph_125_three_clique_partition_oriented_cross_bound

Topic: graphs   Node: 496506ed40ca

Provenance: helper lemma. Edge-counting step for the order-125 reduction for OP-110.

For a graph on 125 vertices partitioned into three cliques, with at most 2583 graph edges, each part has at least seven vertices and every oriented subdigraph has at most 41 arcs between the parts.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
private lemma in833_arith125 (a b c x : ℕ) (hs : a + b + c = 125)
    (h : a * (a - 1) + b * (b - 1) + c * (c - 1) + 2*x ≤ 5166) :
    7 ≤ a ∧ 7 ≤ b ∧ 7 ≤ c ∧ x ≤ 41 := by
  have hprod (n : ℕ) : n * (n - 1) + n = n*n := by
    cases n with
    | zero => simp
    | succ n => simp; ring
  have ha := hprod a
  have hb := hprod b
  have hc := hprod c
  have hsum : a*a + b*b + c*c + 2*x ≤ 5291 := by nlinarith
  have hx : x ≤ 41 := by
    have h1 : (0:ℤ) ≤ ((a:ℤ) - b)^2 := sq_nonneg _
    have h2 : (0:ℤ) ≤ ((b:ℤ) - c)^2 := sq_nonneg _
    have h3 : (0:ℤ) ≤ ((a:ℤ) - c)^2 := sq_nonneg _
    have hs' : (a:ℤ) + b + c = 125 := by exact_mod_cast hs
    have hh' : (a:ℤ)*a + b*b + c*c + 2*x ≤ 5291 := by exact_mod_cast hsum
    have out : (x:ℤ) ≤ 41 := by nlinarith
    exact_mod_cast out
  have hsize (p q r : ℕ) (hs : p+q+r=125)
      (hh : p*p + q*q + r*r ≤ 5291) : 7 ≤ p := by
    by_contra hp
    have hp' : p ≤ 6 := by omega
    have hs' : (p:ℤ) + q + r = 125 := by exact_mod_cast hs
    have hh' : (p:ℤ)*p + q*q + r*r ≤ 5291 := by exact_mod_cast hh
    have hp'' : (p:ℤ) ≤ 6 := by exact_mod_cast hp'
    have hn : (0:ℤ) ≤ p := by exact_mod_cast Nat.zero_le p
    have hq : (0:ℤ) ≤ q := by exact_mod_cast Nat.zero_le q
    have hr : (0:ℤ) ≤ r := by exact_mod_cast Nat.zero_le r
    have hdiff : (0:ℤ) ≤ ((q:ℤ)-(r:ℤ))^2 := sq_nonneg _
    have hbig : (0:ℤ) ≤ ((q:ℤ)+(r:ℤ)-119) * ((q:ℤ)+(r:ℤ)+119) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (p:ℤ)]
  have hh : a*a+b*b+c*c ≤ 5291 := by omega
  refine ⟨hsize a b c hs hh, ?_, ?_, hx⟩
  · apply hsize b a c <;> omega
  · apply hsize c a b <;> omega

theorem graph_125_three_clique_partition_oriented_cross_bound
    (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj]
    (D : Digraph (Fin 125)) [DecidableRel D.Adj] (col : Fin 125 → Fin 3)
    (hclique : ∀ u v, col u = col v → u ≠ v → G.Adj u v)
    (hsub : ∀ u v, D.Adj u v → G.Adj u v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hedges : G.edgeFinset.card ≤ 2583) :
    (∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card) ∧
    (∑ v : Fin 125, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card) ≤ 41 := by
  classical
  let S : Fin 3 → Finset (Fin 125) := fun i => Finset.univ.filter fun v => col v = i
  let n : Fin 3 → ℕ := fun i => (S i).card
  let cross : ℕ := ∑ v : Fin 125, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card
  have hsizes : n 0 + n 1 + n 2 = 125 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := col) (s := (Finset.univ : Finset (Fin 125)))
        (t := (Finset.univ : Finset (Fin 3))) (by simp)
    simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Nat.add_zero] at h
    change 125 = n 0 + (n 1 + n 2) at h
    omega
  have hbound := graph_clique_partition_oriented_cross_degree_bound (Fin 125) (Fin 3) G D col hclique hsub hori
  change (∑ i : Fin 3, n i * (n i - 1)) + 2 * cross ≤ 2 * G.edgeFinset.card at hbound
  have hre : (∑ i : Fin 3, n i * (n i - 1)) =
      n 0 * (n 0 - 1) + n 1 * (n 1 - 1) + n 2 * (n 2 - 1) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Nat.add_zero]
    omega
  rw [hre] at hbound
  have ht : n 0 * (n 0 - 1) + n 1 * (n 1 - 1) + n 2 * (n 2 - 1) + 2*cross ≤ 5166 := by omega
  have h := in833_arith125 (n 0) (n 1) (n 2) cross hsizes ht
  constructor
  · intro i
    change 7 ≤ n i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
  · exact h.2.2.2
