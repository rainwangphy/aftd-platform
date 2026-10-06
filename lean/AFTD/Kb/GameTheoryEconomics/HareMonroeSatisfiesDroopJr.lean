import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsHareMonroeCommittee
import AFTD.Kb.GameTheoryEconomics.IsDroopJr
import AFTD.Kb.GameTheoryEconomics.MonroeExistsHeavy
import AFTD.Kb.GameTheoryEconomics.MonroeExchange

/-!
# hare_monroe_satisfies_droop_jr

Topic: social_choice   Node: cf22b0956cf0

Provenance: original. Related work: answers the open case of Justified Representation: From Hare to Droop, arXiv:2508.00811, App., after Prop. 2 / Table 1 note d (Monroe satisfies Droop-JR when k divides n; other n, k open): holds for all n and k

Every committee selected by the (Hare) Monroe rule satisfies Droop-JR, for all n and k. This answers the open question of Justified Representation: From Hare to Droop (arXiv:2508.00811, App., after Prop. 2), which proved it only when k divides n.
-/

/-- Every committee selected by the (Hare) Monroe rule satisfies Droop-JR, for all n and k. This answers the open question of Justified Representation: From Hare to Droop (arXiv:2508.00811, App., after Prop. 2), which proved it only when k divides n. -/
theorem hare_monroe_satisfies_droop_jr {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ)
    (W : Finset (Fin m)) (hW : is_hare_monroe_committee A k W) : is_droop_jr A k W := by
  obtain ⟨π, hv, hopt⟩ := hW
  intro S hS ⟨c', hc'⟩
  by_contra hno
  push Not at hno
  have hun : ∀ i ∈ S, π i ∉ A i := fun i hi h => hno i hi (π i) (hv.2.1 i) h
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos S.card with h | h
    · rw [h] at hS; simp at hS
    · exact h
  obtain ⟨i₀, hi₀⟩ := hSne
  have hc'W : c' ∉ W := fun h => hno i₀ hi₀ c' h (hc' i₀ hi₀)
  obtain ⟨c, hcW, hheavy⟩ := monroe_exists_heavy k W π hv S hS
  obtain ⟨π', hv', hsc⟩ := monroe_exchange A k W π hv c c' hcW hc'W S hc' hun
  have hle := hopt _ π' hv'
  have hP : ((Finset.univ.filter fun i => π i = c).filter fun i => i ∉ S).card +
      (S.filter fun i => π i = c).card = (Finset.univ.filter fun i => π i = c).card := by
    have : (S.filter fun i => π i = c).card =
        ((Finset.univ.filter fun i => π i = c).filter fun i => i ∈ S).card := by
      congr 1; ext v; simp [and_comm]
    rw [this, add_comm]; exact Finset.card_filter_add_card_filter_not _
  omega
