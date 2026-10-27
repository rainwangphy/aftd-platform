import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsCoeffTEqSum
import AFTD.Kb.Tcs.SimpleGraphColoringTwoColoursConstOnBipartition

/-!
# simple_graph_t_chromatic_ps_coeff_t_two_of_edge

Topic: graphs   Node: 0bed78025a1a

Provenance: helper lemma. arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(3) with the parts in the order given by b

Let G be a connected finite simple graph with a proper 2-coloring b : V → Fin 2 and an edge u0 w0 with b u0 = 0, b w0 = 1. Let s0, s1 be the numbers of vertices with b = 0 and b = 1. Then the coefficient of t^2 in ps_n(Z_G(x; t)) equals the sum over ordered pairs (j1, j2) of distinct elements of Fin n of q^(s0 j1 + s1 j2).
-/

theorem simple_graph_t_chromatic_ps_coeff_t_two_of_edge_fin_two (a : Fin 2) : ¬ a = 0 ↔ a = 1 := by fin_cases a <;> decide

theorem simple_graph_t_chromatic_ps_coeff_t_two_of_edge {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hconn : G.Connected) (b : G.Coloring (Fin 2)) (u0 w0 : V) (hb0 : b u0 = 0) (hb1 : b w0 = 1)
    (hadj : G.Adj u0 w0) :
    (simple_graph_t_chromatic_principal_specialization G n).coeff 2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
        Polynomial.X ^ ((Finset.univ.filter (fun v => b v = 0)).card * (p.1 : ℕ) +
                        (Finset.univ.filter (fun v => b v = 1)).card * (p.2 : ℕ)) := by
  classical
  rw [simple_graph_t_chromatic_ps_coeff_t_eq_sum]
  let φ : Fin n × Fin n → V → Fin n := fun p v => if b v = 0 then p.1 else p.2
  have hφv : ∀ p : Fin n × Fin n, p.1 ≠ p.2 → ∀ x y, G.Adj x y → φ p x ≠ φ p y := by
    intro p hp x y h
    have hb := b.valid h
    simp only [φ]
    by_cases hx : b x = 0 <;> by_cases hy : b y = 0
    · exact absurd (hx.trans hy.symm) hb
    · rw [if_pos hx, if_neg hy]; exact hp
    · rw [if_neg hx, if_pos hy]; exact fun e => hp e.symm
    · rw [simple_graph_t_chromatic_ps_coeff_t_two_of_edge_fin_two] at hx hy; exact absurd (hx.trans hy.symm) hb
  have hW : ∀ p : Fin n × Fin n, ∑ v : V, (φ p v : ℕ) =
      (Finset.univ.filter (fun v => b v = 0)).card * (p.1 : ℕ) +
        (Finset.univ.filter (fun v => b v = 1)).card * (p.2 : ℕ) := by
    intro p
    simp only [φ]
    rw [show (fun v => ((if b v = 0 then p.1 else p.2 : Fin n) : ℕ)) =
        (fun v => if b v = 0 then (p.1 : ℕ) else (p.2 : ℕ)) from funext fun v => by split_ifs <;> rfl]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    congr 2
    exact congrArg Finset.card (Finset.filter_congr (fun v _ => simple_graph_t_chromatic_ps_coeff_t_two_of_edge_fin_two (b v)))
  symm
  refine Finset.sum_bij'
    (fun p hp => SimpleGraph.Coloring.mk (φ p)
      (fun h e => hφv p (Finset.mem_filter.1 hp).2 _ _ h e))
    (fun c _ => (c u0, c w0)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : Finset.univ.image (SimpleGraph.Coloring.mk (φ p)
        (fun h e => hφv p hp' _ _ h e) : V → Fin n) = {p.1, p.2} := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
        obtain ⟨v, rfl⟩ := hy
        show φ p v ∈ _
        simp only [φ]; split_ifs <;> simp
      · apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        rcases hy with rfl | rfl
        · exact ⟨u0, by show φ p u0 = _; simp [φ, hb0]⟩
        · exact ⟨w0, by show φ p w0 = _; simp [φ, hb1]⟩
    rw [this, Finset.card_pair hp']
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact c.valid hadj
  · intro p hp
    exact Prod.ext (by show (if b u0 = 0 then p.1 else p.2) = p.1; simp [hb0])
      (by show (if b w0 = 0 then p.1 else p.2) = p.2; simp [hb1])
  · intro c hc
    have hc' := (Finset.mem_filter.1 hc).2
    ext v
    show (φ (c u0, c w0) v : ℕ) = c v
    rw [simple_graph_coloring_two_colours_const_on_bipartition G n hconn b u0 w0 hb0 hb1 hadj c hc' v]
  · intro p hp
    rw [← hW p]
    rfl
