import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFree

/-!
# odd_cycle_is_claw_free

Topic: graphs   Node: 27132b6494de

Provenance: helper lemma. arXiv:2611.09072 Claw-free minimal factor-critical and bicritical graphs, proof of Theorem 1.4

For every integer n ≥ 1, the odd cycle graph C_{2n+1} is claw-free.
-/

theorem odd_cycle_is_claw_free_of_degree_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, G.degree v ≤ 2) : IsClawFree G := by
  rintro ⟨f⟩
  set v : V := f (Sum.inl 0)
  set a : V := f (Sum.inr 0)
  set b : V := f (Sum.inr 1)
  set c : V := f (Sum.inr 2)
  have ha : a ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    have hadj : (completeBipartiteGraph (Fin 1) (Fin 3)).Adj (Sum.inl 0) (Sum.inr 0) := by
      simp [completeBipartiteGraph_adj]
    exact f.map_rel_iff.mpr hadj
  have hb : b ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    have hadj : (completeBipartiteGraph (Fin 1) (Fin 3)).Adj (Sum.inl 0) (Sum.inr 1) := by
      simp [completeBipartiteGraph_adj]
    exact f.map_rel_iff.mpr hadj
  have hc : c ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    have hadj : (completeBipartiteGraph (Fin 1) (Fin 3)).Adj (Sum.inl 0) (Sum.inr 2) := by
      simp [completeBipartiteGraph_adj]
    exact f.map_rel_iff.mpr hadj
  have hab : a ≠ b := by
    intro h
    have := f.injective h
    contradiction
  have hbc : b ≠ c := by
    intro h
    have := f.injective h
    contradiction
  have hac : a ≠ c := by
    intro h
    have := f.injective h
    contradiction
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro h
      simp only [Finset.mem_singleton] at h
      exact hbc h
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hab h
      · exact hac h
  have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hdeg_v := hdeg v
  rw [← SimpleGraph.degree] at hle
  omega

/-- The odd cycle graph C_{2n+1} is claw-free for any n ≥ 1. -/
theorem odd_cycle_is_claw_free (n : ℕ) (hn : 1 ≤ n) :
    IsClawFree (SimpleGraph.cycleGraph (2 * n + 1)) := by
  apply odd_cycle_is_claw_free_of_degree_le_two
  intro v
  rcases n with _ | k
  · omega
  · have h : (SimpleGraph.cycleGraph (2 * (k + 1) + 1)).degree v = 2 :=
      SimpleGraph.cycleGraph_degree_three_le
    omega
