import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorCriticalAnticompleteCutSideEven
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# nontrivial_factorcritical_graph_connected

Topic: graphs   Node: 65e28f3dc6b3

Provenance: helper lemma. Classical factor-critical connectivity, used in the OP-1957 unrestricted twin-bridge route.

A factor-critical graph with at least two vertices is connected.
-/

theorem nontrivial_factorcritical_graph_connected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hcrit : is_k_factor_critical G 1) (x y : V) (hxy : x ≠ y) : G.Connected := by
  classical
  haveI : Nonempty V := ⟨x⟩
  refine ⟨?_⟩
  intro a b
  by_contra hn
  let S : Finset V := Finset.univ.filter (fun v => G.Reachable a v)
  have haS : a ∈ S := by simp [S, SimpleGraph.Reachable.refl]
  have hbS : b ∉ S := by simpa [S] using hn
  have hacross : ∀ c ∈ S, ∀ e ∉ S, ¬ G.Adj c e := by
    intro c hc e he hce
    apply he
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.trans hce.reachable
  let B := Finset.univ \ insert b S
  have hd : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro c hc hcb
    simp [B, hc] at hcb
  have hcross : ∀ c ∈ S, ∀ e ∈ B, ¬ G.Adj c e := by
    intro c hc e he
    apply hacross c hc e
    have he' : e ≠ b ∧ e ∉ S := by simpa [B] using he
    exact he'.2
  have hcut : ((Finset.univ : Finset V) \ (S ∪ B)).card = 1 := by
    have hs : (Finset.univ : Finset V) \ (S ∪ B) = {b} := by
      ext c
      by_cases hcb : c = b <;> simp [B, hcb, hbS]
    rw [hs, Finset.card_singleton]
  have hevenS := factor_critical_anticomplete_cut_side_even G 1 hcrit S B hd hcross hcut
  let C := (Finset.univ : Finset V) \ S
  have hd' : Disjoint (S.erase a) C := by
    apply Finset.disjoint_left.mpr
    intro c hc hcc
    exact (Finset.mem_sdiff.mp hcc).2 (Finset.mem_of_mem_erase hc)
  have hcross' : ∀ c ∈ S.erase a, ∀ e ∈ C, ¬ G.Adj c e := by
    intro c hc e he
    exact hacross c (Finset.mem_of_mem_erase hc) e (Finset.mem_sdiff.mp he).2
  have hcut' : ((Finset.univ : Finset V) \ ((S.erase a) ∪ C)).card = 1 := by
    have hs : (Finset.univ : Finset V) \ ((S.erase a) ∪ C) = {a} := by
      ext c
      by_cases hca : c = a <;> simp [C, hca, haS]
    rw [hs, Finset.card_singleton]
  have hevenS' := factor_critical_anticomplete_cut_side_even G 1 hcrit (S.erase a) C hd' hcross' hcut'
  rw [Finset.card_erase_of_mem haS] at hevenS'
  obtain ⟨t, ht⟩ := hevenS
  obtain ⟨s, hs⟩ := hevenS'
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, haS⟩
  omega
