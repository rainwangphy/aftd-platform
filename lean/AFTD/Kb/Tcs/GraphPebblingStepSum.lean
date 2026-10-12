import AFTD.Prelude
import AFTD.Kb.Tcs.GraphPebblingStep

/-!
# graph_pebbling_step_sum

Topic: graphs   Node: 8e4ac0a59f89

Provenance: helper lemma. Sanity lemma for graph_pebbling_step (arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Sec. 2).

A pebbling step lowers the size ‖c‖ = Σ_v c(v) by exactly one.
-/

theorem graph_pebbling_step_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {c c' : V → ℕ} (h : graph_pebbling_step G c c') : ∑ v, c' v + 1 = ∑ v, c v := by
  obtain ⟨u, v, huv, hu, hc'⟩ := h
  have hne : u ≠ v := G.ne_of_adj huv
  have key : ∀ x, c' x + (if x = u then 2 else 0) = c x + (if x = v then 1 else 0) := by
    intro x
    rw [hc']
    by_cases hxv : x = v
    · subst hxv
      simp [hne.symm]
    · by_cases hxu : x = u
      · subst hxu
        simp [hxv]
        omega
      · simp [hxu, hxv]
  have hs := Finset.sum_congr rfl (fun x (_ : x ∈ (Finset.univ : Finset V)) => key x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    at hs
  simp only [Finset.mem_univ, if_true] at hs
  omega
