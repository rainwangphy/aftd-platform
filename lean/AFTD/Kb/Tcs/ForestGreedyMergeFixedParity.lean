import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep

/-!
# forest_greedy_merge_fixed_parity

Topic: online_algorithms   Node: 97ea1ee2b501

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

If the first endpoint has fixed discrepancy parity, one greedy step has fixed output parity for all partner values and tie coins.
-/

theorem forest_greedy_merge_fixed_parity
    (α β : Type) [Fintype α] [Fintype β] (X : α → ℤ) (Y : β → ℤ)
    (h : ∃ t : ℤ, ∀ a, X a % 2 = t) :
    ∃ t : ℤ, ∀ p : α × β × Bool,
      forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2 % 2 = t := by
  obtain ⟨t, ht⟩ := h
  refine ⟨(t + 1) % 2, ?_⟩
  intro p
  specialize ht p.1
  unfold forest_greedy_signed_step
  split_ifs <;> omega
