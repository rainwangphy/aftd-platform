import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep
import AFTD.Kb.Tcs.ForestGreedyThresholdEventCount
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# forest_greedy_high_tail_step

Topic: online_algorithms   Node: deaaf24f9925

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For two independent nonempty finite uniform integer laws and a fair tie coin, the updated tail at k is at most the first tail at k+1 plus the product of the two tails at k-1.
-/

theorem forest_greedy_high_tail_step
    (α β : Type) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (X : α → ℤ) (Y : β → ℤ) (k : ℤ) :
    (((Finset.univ.filter (fun p : α × β × Bool =>
      k ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)).card : ℝ) /
        (Fintype.card (α × β × Bool) : ℝ)) ≤
      (((Finset.univ.filter (fun a => k + 1 ≤ X a)).card : ℝ) / Fintype.card α) +
      (((Finset.univ.filter (fun a => k - 1 ≤ X a)).card : ℝ) / Fintype.card α) *
      (((Finset.univ.filter (fun b => k - 1 ≤ Y b)).card : ℝ) / Fintype.card β) := by
  classical
  let hi : Finset α := Finset.univ.filter (fun a => k + 1 ≤ X a)
  let mid : Finset α := Finset.univ.filter (fun a => k - 1 ≤ X a ∧ X a ≤ k)
  let lo : Finset α := Finset.univ.filter (fun a => k - 1 ≤ X a)
  let ylo : Finset β := Finset.univ.filter (fun b => k - 1 ≤ Y b)
  let allow : Finset (β × Bool) := Finset.univ.filter (fun p =>
    k - 1 < Y p.1 ∨ (k - 1 = Y p.1 ∧ p.2 = true))
  let ev : Finset (α × β × Bool) := Finset.univ.filter (fun p =>
    k ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)
  have hm : mid.card ≤ lo.card := by
    apply Finset.card_le_card
    intro a ha
    have h : k - 1 ≤ X a ∧ X a ≤ k := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩
  have hs : allow.card ≤ 2 * ylo.card := by
    have hsub : allow ⊆ ylo ×ˢ (Finset.univ : Finset Bool) := by
      intro p hp
      have hp' : k - 1 < Y p.1 ∨ (k - 1 = Y p.1 ∧ p.2 = true) := (Finset.mem_filter.mp hp).2
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · rcases hp' with hp' | ⟨hp', _⟩ <;> omega
      · exact Finset.mem_univ _
    have hc := Finset.card_le_card hsub
    simpa [Finset.card_product, Nat.mul_comm] using hc
  have hc : ev.card ≤ hi.card * Fintype.card (β × Bool) + mid.card * allow.card := by
    simpa [ev, hi, mid, allow] using forest_greedy_threshold_event_count α β X Y k
  have hmul : mid.card * allow.card ≤ lo.card * (2 * ylo.card) := Nat.mul_le_mul hm hs
  have hn : ev.card ≤ hi.card * (2 * Fintype.card β) + lo.card * (2 * ylo.card) := by
    simp only [Fintype.card_prod, Fintype.card_bool] at hc
    nlinarith
  have hr : (ev.card : ℝ) ≤ (hi.card : ℝ) * (2 * (Fintype.card β : ℝ)) +
      (lo.card : ℝ) * (2 * (ylo.card : ℝ)) := by exact_mod_cast hn
  have hp : (0 : ℝ) < Fintype.card α := by exact_mod_cast (Fintype.card_pos (α := α))
  have hq : (0 : ℝ) < Fintype.card β := by exact_mod_cast (Fintype.card_pos (α := β))
  have hden : (0 : ℝ) ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * 2 := by positivity
  have hreal : (ev.card : ℝ) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) * 2) ≤
      (hi.card : ℝ) / Fintype.card α +
        ((lo.card : ℝ) / Fintype.card α) * ((ylo.card : ℝ) / Fintype.card β) := by
    calc
      _ ≤ ((hi.card : ℝ) * (2 * (Fintype.card β : ℝ)) +
          (lo.card : ℝ) * (2 * (ylo.card : ℝ))) /
          ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) * 2) :=
        div_le_div_of_nonneg_right hr hden
      _ = _ := by field_simp [ne_of_gt hp, ne_of_gt hq]
  simpa [ev, hi, lo, ylo, Fintype.card_prod, Nat.cast_mul, mul_assoc] using hreal
