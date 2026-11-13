import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep
import AFTD.Kb.Tcs.ForestGreedyThresholdEventCount
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# forest_greedy_refined_tail_step

Topic: online_algorithms   Node: e0672be2eaa2

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For two independent uniform finite integer laws and a fair tie coin, the probability that a greedy update reaches threshold k is bounded by the first-law tail at k+1 plus the mass between k-1 and k times the chance that the partner-coin pair permits an increase from k-1.
-/

theorem forest_greedy_refined_tail_step
    (α β : Type) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (X : α → ℤ) (Y : β → ℤ) (k : ℤ) :
  (((Finset.univ.filter (fun p : α × β × Bool =>
    k ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)).card : ℝ) /
    (Fintype.card (α × β × Bool) : ℝ)) ≤
  (((Finset.univ.filter (fun a => k + 1 ≤ X a)).card : ℝ) / Fintype.card α) +
  ((((Finset.univ.filter (fun a => k - 1 ≤ X a)).card : ℝ) / Fintype.card α) -
   (((Finset.univ.filter (fun a => k + 1 ≤ X a)).card : ℝ) / Fintype.card α)) *
  (((Finset.univ.filter (fun p : β × Bool =>
    k - 1 < Y p.1 ∨ (k - 1 = Y p.1 ∧ p.2 = true))).card : ℝ) /
    (Fintype.card (β × Bool) : ℝ)) := by
  classical
  let hi : Finset α := Finset.univ.filter (fun a => k + 1 ≤ X a)
  let mid : Finset α := Finset.univ.filter (fun a => k - 1 ≤ X a ∧ X a ≤ k)
  let lo : Finset α := Finset.univ.filter (fun a => k - 1 ≤ X a)
  let allow : Finset (β × Bool) := Finset.univ.filter (fun p =>
    k - 1 < Y p.1 ∨ (k - 1 = Y p.1 ∧ p.2 = true))
  let ev : Finset (α × β × Bool) := Finset.univ.filter (fun p =>
    k ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)
  have heq : lo = hi ∪ mid := by
    ext a
    simp only [lo, hi, mid, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint hi mid := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hh : k + 1 ≤ X a := (Finset.mem_filter.mp ha).2
    have hm : k - 1 ≤ X a ∧ X a ≤ k := (Finset.mem_filter.mp hb).2
    omega
  have hpart : lo.card = hi.card + mid.card := by rw [heq, Finset.card_union_of_disjoint hd]
  have hc : ev.card ≤ hi.card * Fintype.card (β × Bool) + mid.card * allow.card := by
    simpa [ev, hi, mid, allow] using forest_greedy_threshold_event_count α β X Y k
  have hr : (ev.card : ℝ) ≤ (hi.card : ℝ) * (Fintype.card (β × Bool) : ℝ) +
      (mid.card : ℝ) * (allow.card : ℝ) := by exact_mod_cast hc
  have hpartR : (lo.card : ℝ) = (hi.card : ℝ) + (mid.card : ℝ) := by exact_mod_cast hpart
  have hp : (0 : ℝ) < Fintype.card α := by exact_mod_cast (Fintype.card_pos (α := α))
  have hq : (0 : ℝ) < Fintype.card (β × Bool) := by
    exact_mod_cast (Fintype.card_pos (α := β × Bool))
  have hreal : (ev.card : ℝ) / ((Fintype.card α : ℝ) * Fintype.card (β × Bool)) ≤
      (hi.card : ℝ) / Fintype.card α +
      ((lo.card : ℝ) / Fintype.card α - (hi.card : ℝ) / Fintype.card α) *
        ((allow.card : ℝ) / Fintype.card (β × Bool)) := by
    calc
      _ ≤ ((hi.card : ℝ) * (Fintype.card (β × Bool) : ℝ) +
          (mid.card : ℝ) * (allow.card : ℝ)) /
          ((Fintype.card α : ℝ) * Fintype.card (β × Bool)) :=
        div_le_div_of_nonneg_right hr (le_of_lt (mul_pos hp hq))
      _ = _ := by rw [hpartR]; field_simp [ne_of_gt hp, ne_of_gt hq] <;> ring
  simpa [ev, hi, lo, allow, Fintype.card_prod, Nat.cast_mul] using hreal
