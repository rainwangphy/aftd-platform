import AFTD.Prelude
import AFTD.Kb.Tcs.Op869IncidenceDegreeCount
import AFTD.Kb.Tcs.Op869DoubleCount
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_repeated_color_incidence

Topic: online_algorithms   Node: e1948232bd16

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.5, the incidence-counting step for the reserved copies.

Suppose there are KqD copies and fewer than K colors, and every copy contains at least q colors. If 1 ≤ q ≤ K and D ≥ 1, at least q colors occur in at least qD copies each.
-/

theorem op869_repeated_color_incidence {α β : Type} [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β)
    (R : α → β → Prop) [DecidableRel R] (K q D : ℕ) :
    1 ≤ q → q ≤ K → 1 ≤ D → A.card = K * q * D → B.card < K →
    (∀ a ∈ A, q ≤ (B.filter (R a)).card) →
    q ≤ (B.filter (fun b => q * D ≤ (A.filter (fun a => R a b)).card)).card := by
  intro hq hqK hD hA hB hd
  let E : α → Finset β := fun a => B.filter (R a)
  have hE : ∀ a ∈ A, E a ⊆ B := by
    intro a ha b hb
    exact (Finset.mem_filter.mp hb).1
  have hK : 1 ≤ K := le_trans hq hqK
  have hs : 1 ≤ q * D := Nat.mul_pos hq hD
  have hQA : q * D ≤ A.card := by
    rw [hA]
    have := Nat.mul_le_mul_right (q * D) hK
    simpa [Nat.mul_assoc] using this
  have hcard : (B.filter (fun b => q * D ≤ (A.filter (fun a => b ∈ E a)).card)) =
      B.filter (fun b => q * D ≤ (A.filter (fun a => R a b)).card) := by
    apply Finset.filter_congr
    intro b hb
    have heq : (A.filter (fun a => b ∈ E a)) = A.filter (fun a => R a b) := by
      ext a
      simp [E, hb]
    rw [heq]
  have hdc := op869_double_count A B E q (q * D) hE hd hQA
  rw [hcard, hA] at hdc
  let H := (B.filter (fun b => q * D ≤ (A.filter (fun a => R a b)).card)).card
  change K * q * D * q ≤ B.card * (q * D - 1) + (K * q * D - q * D + 1) * H at hdc
  by_contra hnot
  have hH : H ≤ q - 1 := by dsimp [H]; omega
  have hB' : B.card ≤ K - 1 := by omega
  have h1 := Nat.mul_le_mul_right (q * D - 1) hB'
  have h2 := Nat.mul_le_mul_left (K * q * D - q * D + 1) hH
  have hsub : K * q * D - q * D = (K - 1) * (q * D) := by
    have heq : K = (K - 1) + 1 := by omega
    conv_lhs => rw [heq]
    simp only [Nat.add_mul, one_mul, Nat.add_sub_cancel_right, Nat.mul_assoc]
  rw [hsub] at hdc h2
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  obtain ⟨p, hp⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  obtain ⟨s, hs'⟩ : ∃ s, q * D = s + 1 := ⟨q * D - 1, by omega⟩
  have hh : K * q * D = K * (q * D) := by ring
  rw [hh, hs'] at hdc
  rw [hs'] at h1 h2
  simp only [hk, hp, Nat.add_sub_cancel] at hdc h1 h2
  nlinarith
