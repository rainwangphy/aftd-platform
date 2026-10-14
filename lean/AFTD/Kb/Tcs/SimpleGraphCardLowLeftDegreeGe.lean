import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_card_low_left_degree_ge

Topic: graphs   Node: f982f5af5290

Provenance: formalization of a published result. Source: arXiv:2610.14374 (Greedy coloring and simple exponential strengthenings of Brooks' theorem), Lemma 5.

Let G be a finite graph, k a real with k ≥ 2|E(G)|/|V(G)|, and 0 ≤ q < k. For any ordering σ of the vertices, at least (q/(k+q))·|V(G)| vertices have fewer than (k+q)/2 neighbours before them in σ.
-/

theorem simple_graph_card_low_left_degree_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : V ≃ Fin (Fintype.card V)) (k q : ℝ)
    (hk : 2 * (G.edgeFinset.card : ℝ) / Fintype.card V ≤ k) (hq : 0 ≤ q) (hqk : q < k) :
    q / (k + q) * Fintype.card V ≤
      ((Finset.univ.filter (fun v =>
        (((Finset.univ.filter (fun u => G.Adj u v ∧ σ u < σ v)).card : ℝ) < (k + q) / 2))).card : ℝ) := open Finset in by
  set ld : V → ℕ := fun v => (univ.filter (fun u => G.Adj u v ∧ σ u < σ v)).card with hld
  set rd : V → ℕ := fun v => (univ.filter (fun u => G.Adj v u ∧ σ v < σ u)).card with hrd
  have hsplit : ∀ v, ld v + rd v = G.degree v := by
    intro v
    rw [← G.card_neighborFinset_eq_degree]
    have h : G.neighborFinset v = (univ.filter (fun u => G.Adj u v ∧ σ u < σ v)) ∪
        (univ.filter (fun u => G.Adj v u ∧ σ v < σ u)) := by
      ext u
      simp only [SimpleGraph.mem_neighborFinset, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · intro h
        rcases lt_trichotomy (σ u) (σ v) with h1 | h1 | h1
        · exact Or.inl ⟨h.symm, h1⟩
        · exact absurd (σ.injective h1 ▸ h) G.irrefl
        · exact Or.inr ⟨h, h1⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact h.symm
        · exact h
    rw [h, card_union_of_disjoint]
    rw [disjoint_filter]
    intro u _ h1 h2
    exact absurd (h1.2.trans h2.2) (lt_irrefl _)
  have hswap : ∑ v, ld v = ∑ v, rd v := by
    simp only [hld, hrd, card_filter]
    exact Finset.sum_comm
  have hE : ∑ v, ld v = G.edgeFinset.card := by
    have h2 := G.sum_degrees_eq_twice_card_edges
    have : ∑ v, G.degree v = ∑ v, ld v + ∑ v, rd v := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun v _ => (hsplit v).symm)
    omega
  set Lo := univ.filter (fun v => (ld v : ℝ) < (k + q) / 2) with hLo
  set Hi := univ.filter (fun v => ¬ (ld v : ℝ) < (k + q) / 2) with hHi
  have hcard : Lo.card + Hi.card = Fintype.card V := by rw [card_filter_add_card_filter_not, card_univ]
  have hHi_le : (Hi.card : ℝ) * ((k + q) / 2) ≤ G.edgeFinset.card := by
    have h1 : Hi.card • ((k + q) / 2) ≤ ∑ v ∈ Hi, (ld v : ℝ) := by
      apply card_nsmul_le_sum
      intro v hv
      simp only [hHi, mem_filter, mem_univ, true_and, not_lt] at hv
      exact hv
    rw [nsmul_eq_mul] at h1
    have h2 : ∑ v ∈ Hi, (ld v : ℝ) ≤ ∑ v, (ld v : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    have h3 : ∑ v, (ld v : ℝ) = G.edgeFinset.card := by
      rw [← Nat.cast_sum, hE]
    linarith
  have hkq : 0 < k + q := by linarith
  have hcardR : (Lo.card : ℝ) + Hi.card = Fintype.card V := by exact_mod_cast hcard
  show q / (k + q) * Fintype.card V ≤ (Lo.card : ℝ)
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · have : Lo.card = 0 := by omega
    rw [this, hn]; simp
  · have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    have hE2 : 2 * (G.edgeFinset.card : ℝ) ≤ k * Fintype.card V := by
      rwa [div_le_iff₀ hnR] at hk
    rw [div_mul_eq_mul_div, div_le_iff₀ hkq]
    nlinarith
