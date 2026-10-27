import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsCoeffCoeff

/-!
# simple_graph_t_chromatic_ps_min_add_max_q_degree

Topic: graphs   Node: 03d5286aec5d

Provenance: helper lemma. arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(1), the step (n-1)|V| = d + D

For a finite simple graph G and n ∈ ℕ, if d and D are the least and greatest exponents j of q such that some coefficient of t^k q^j in ps_n(Z_G(x; t)) is nonzero, then (n-1)|V| = d + D.
-/

theorem simple_graph_t_chromatic_ps_min_add_max_q_degree_mem {V : Type*} [Fintype V] (G : SimpleGraph V) (n j : ℕ) :
    j ∈ {j | ∃ k, ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j ≠ 0} ↔
      ∃ c : G.Coloring (Fin n), ∑ v : V, (c v : ℕ) = j := by
  simp only [Set.mem_setOf_eq, simple_graph_t_chromatic_ps_coeff_coeff, ne_eq, Fintype.card_eq_zero_iff, not_isEmpty_iff]
  constructor
  · rintro ⟨k, ⟨c, -, hc⟩⟩; exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩; exact ⟨_, ⟨c, rfl, hc⟩⟩

theorem simple_graph_t_chromatic_ps_min_add_max_q_degree {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) (d D : ℕ)
    (hd : IsLeast {j | ∃ k, ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j ≠ 0} d)
    (hD : IsGreatest {j | ∃ k, ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j ≠ 0} D) :
    (n - 1) * Fintype.card V = d + D := by
  classical
  obtain ⟨c0, hc0⟩ := (simple_graph_t_chromatic_ps_min_add_max_q_degree_mem G n d).1 hd.1
  obtain ⟨c1, hc1⟩ := (simple_graph_t_chromatic_ps_min_add_max_q_degree_mem G n D).1 hD.1
  let r : G.Coloring (Fin n) → G.Coloring (Fin n) := fun c =>
    SimpleGraph.Coloring.mk (fun v => Fin.rev (c v)) (fun h e => c.valid h (Fin.rev_injective e))
  have hW : ∀ c : G.Coloring (Fin n), ∑ v : V, ((r c) v : ℕ) + ∑ v : V, (c v : ℕ) = (n - 1) * Fintype.card V := by
    intro c
    rw [← Finset.sum_add_distrib]
    have : ∀ v, ((r c) v : ℕ) + (c v : ℕ) = n - 1 := by
      intro v
      show ((Fin.rev (c v) : Fin n) : ℕ) + (c v : ℕ) = n - 1
      rw [Fin.val_rev]; have := (c v).isLt; omega
    simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have h1 := hD.2 ((simple_graph_t_chromatic_ps_min_add_max_q_degree_mem G n _).2 ⟨r c0, rfl⟩)
  have h2 := hd.2 ((simple_graph_t_chromatic_ps_min_add_max_q_degree_mem G n _).2 ⟨r c1, rfl⟩)
  have e0 := hW c0
  have e1 := hW c1
  omega
