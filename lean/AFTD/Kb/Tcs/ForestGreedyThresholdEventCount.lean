import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# forest_greedy_threshold_event_count

Topic: online_algorithms   Node: 05707f2876a6

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For two finite uniform endpoint populations and a fair tie coin, the number of greedy updates reaching an integer threshold is bounded by the sum of the already-high endpoint count and the product of the near-threshold endpoint count and the eligible partner-coin count.
-/

private lemma forest_greedy_threshold_aux (x y k : ℤ) (coin : Bool)
    (h : k ≤ forest_greedy_signed_step x y coin) :
    k + 1 ≤ x ∨ (k - 1 ≤ x ∧ x ≤ k ∧
      (k - 1 < y ∨ (k - 1 = y ∧ coin = true))) := by
  unfold forest_greedy_signed_step at h
  split_ifs at h <;> simp_all <;> omega

theorem forest_greedy_threshold_event_count
    (α β : Type) [Fintype α] [Fintype β] (X : α → ℤ) (Y : β → ℤ) (k : ℤ) :
    (Finset.univ.filter (fun p : α × β × Bool =>
      k ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)).card ≤
    ((Finset.univ.filter (fun a => k + 1 ≤ X a)).card * Fintype.card (β × Bool)) +
    ((Finset.univ.filter (fun a => k - 1 ≤ X a ∧ X a ≤ k)).card *
      (Finset.univ.filter (fun p : β × Bool =>
        k - 1 < Y p.1 ∨ (k - 1 = Y p.1 ∧ p.2 = true))).card) := by
  classical
  let hi : Finset α := Finset.univ.filter (fun a => k + 1 ≤ X a)
  let mid : Finset α := Finset.univ.filter (fun a => k - 1 ≤ X a ∧ X a ≤ k)
  let allow : Finset (β × Bool) := Finset.univ.filter (fun p =>
    k - 1 < Y p.1 ∨ (k - 1 = Y p.1 ∧ p.2 = true))
  let events : Finset (α × β × Bool) := Finset.univ.filter (fun p =>
    k ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)
  have hsub : events ⊆ (hi ×ˢ Finset.univ) ∪ (mid ×ˢ allow) := by
    intro p hp
    have hp' : k ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2 := by
      simpa [events] using hp
    rcases forest_greedy_threshold_aux (X p.1) (Y p.2.1) k p.2.2 hp' with hhi | ⟨hlo,hupper,hallow⟩
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhi⟩, Finset.mem_univ _⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hlo, hupper⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hallow⟩⟩
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (hi ×ˢ (Finset.univ : Finset (β × Bool))) (mid ×ˢ allow)
  calc
    _ = events.card := rfl
    _ ≤ ((hi ×ˢ Finset.univ) ∪ (mid ×ˢ allow)).card := hc
    _ ≤ (hi ×ˢ (Finset.univ : Finset (β × Bool))).card + (mid ×ˢ allow).card := hu
    _ = _ := by simp [hi, mid, allow, Finset.card_product]
