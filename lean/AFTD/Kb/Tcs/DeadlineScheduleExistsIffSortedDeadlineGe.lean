import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# deadline_schedule_exists_iff_sorted_deadline_ge

Topic: online_algorithms   Node: da497c4b767a

Provenance: formalization of a published result. Source: arXiv:2610.13775 (A 1/2-Approximation for Pandora's Problem with Deadlines), Lemma 2, first part (the feasibility characterization; the O(n²) dynamic program of the second part is not stated).

Boxes i₁, …, i_k with nondecreasing integer deadlines d_{i₁} ≤ … ≤ d_{i_k} can be opened one per round (rounds 1, 2, …), each box i in a round t ≤ d_i, if and only if d_{i_j} ≥ j for every j. (Here box j is indexed from 0, so the condition reads j + 1 ≤ d j.)
-/

theorem deadline_schedule_exists_iff_sorted_deadline_ge (k : ℕ) (d : Fin k → ℕ)
    (hd : Monotone d) :
    (∃ σ : Fin k → ℕ, Function.Injective σ ∧ ∀ j, 1 ≤ σ j ∧ σ j ≤ d j) ↔
      ∀ j : Fin k, j.val + 1 ≤ d j := by
  constructor
  · rintro ⟨σ, h_inj, h_bound⟩ j
    have h_maps : Set.MapsTo σ (Finset.Iic j : Set (Fin k)) (Finset.Icc 1 (d j) : Set ℕ) := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_Iic] at hx
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨(h_bound x).1, (h_bound x).2.trans (hd hx)⟩
    have h_card := Finset.card_le_card_of_injOn σ h_maps h_inj.injOn
    rw [Fin.card_Iic, Nat.card_Icc] at h_card
    omega
  · intro h
    use fun j => j.val + 1
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply Fin.ext
      dsimp at hab
      omega
    · intro j
      exact ⟨Nat.le_add_left 1 j.val, h j⟩
