import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsHareValidAssignment
import AFTD.Kb.GameTheoryEconomics.MonroeCeilLeFloorSucc

/-!
# monroe_exists_heavy

Topic: social_choice   Node: b2d37f3fc204

Counting step: if (W, π) is Hare-valid and |S| > n/(k+1), then some c ∈ W satisfies |π⁻¹(c)| < min(|π⁻¹(c)|, |S|) + |π⁻¹(c) ∩ S|.
-/

/-- The counting step: if `S` has more than `n/(k+1)` voters, some committee member `c` has `|π⁻¹(c)| < min(|π⁻¹(c)|, |S|) + |π⁻¹(c) ∩ S|`. -/
theorem monroe_exists_heavy {n m : ℕ} (k : ℕ) (W : Finset (Fin m)) (π : Fin n → Fin m)
    (hv : is_hare_valid_assignment k W π) (S : Finset (Fin n)) (hS : n < (k + 1) * S.card) :
    ∃ c ∈ W, (Finset.univ.filter fun i => π i = c).card <
      min (Finset.univ.filter fun i => π i = c).card S.card + (S.filter fun i => π i = c).card := by
  obtain ⟨hW, hmap, hload⟩ := hv
  by_contra hcon
  push Not at hcon
  set x := S.card with hx
  have ht : ∀ c ∈ W, (S.filter fun i => π i = c).card ≤
      (Finset.univ.filter fun i => π i = c).card - x := by
    intro c hc; have := hcon c hc; omega
  have hsumS : ∑ c ∈ W, (S.filter fun i => π i = c).card = x :=
    (Finset.card_eq_sum_card_fiberwise (fun i _ => hmap i)).symm
  have hsumN : ∑ c ∈ W, (Finset.univ.filter fun i => π i = c).card = n := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => hmap i)]; simp
  have hle : x ≤ ∑ c ∈ W, ((Finset.univ.filter fun i => π i = c).card - x) :=
    calc x = ∑ c ∈ W, (S.filter fun i => π i = c).card := hsumS.symm
      _ ≤ _ := Finset.sum_le_sum ht
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hS; simp at hS
    · exact h
  by_cases hsmall : x ≤ n / k
  · have hge : ∀ c ∈ W, x ≤ (Finset.univ.filter fun i => π i = c).card :=
      fun c hc => hsmall.trans (hload c hc).1
    have hsum : ∑ c ∈ W, ((Finset.univ.filter fun i => π i = c).card - x) + k * x = n := by
      have h := Finset.sum_congr rfl fun c hc => Nat.sub_add_cancel (hge c hc)
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hW] at h
      omega
    have : (k + 1) * x = k * x + x := by ring
    omega
  · have hz : ∀ c ∈ W, (Finset.univ.filter fun i => π i = c).card - x = 0 := by
      intro c hc
      have := (hload c hc).2
      have := monroe_ceil_le_floor_succ n k
      omega
    rw [Finset.sum_eq_zero hz] at hle
    omega
