import AFTD.Prelude
import AFTD.Kb.Tcs.SauerShelahCardLeSumChoose

/-!
# sauer_shelah_card_le_mul_pow

Topic: combinatorics   Node: a3c42c72f720

Provenance: formalization of a published result. Source: Sauer-Shelah lemma (1972), polynomial form |A| <= (d+1) n^d; standard textbook result (learning theory)

Polynomial form of the Sauer–Shelah lemma. Let 𝒜 be a finite family of subsets of a finite set α with n = |α| ≥ 1. If the VC-dimension of 𝒜 is at most d, then |𝒜| ≤ (d + 1)·n^d.
-/

/-- Polynomial form of Sauer–Shelah: a set family of VC-dimension at most d on n ≥ 1 points has at most (d+1)·n^d members. -/
theorem sauer_shelah_card_le_mul_pow {α : Type*} [Fintype α] [DecidableEq α] (𝒜 : Finset (Finset α))
    (d : ℕ) (hn : 1 ≤ Fintype.card α) (h : 𝒜.vcDim ≤ d) :
    𝒜.card ≤ (d + 1) * (Fintype.card α) ^ d := by
  calc 𝒜.card ≤ ∑ k ∈ Finset.Iic d, (Fintype.card α).choose k :=
        sauer_shelah_card_le_sum_choose 𝒜 d h
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card α) ^ k :=
        Finset.sum_le_sum (fun k _ => Nat.choose_le_pow (Fintype.card α) k)
    _ ≤ (d + 1) * (Fintype.card α) ^ d := by
        have hs := Finset.sum_le_card_nsmul (Finset.Iic d)
          (fun k => (Fintype.card α) ^ k) ((Fintype.card α) ^ d) ?_
        · simp only [smul_eq_mul] at hs
          simpa using hs
        · intro k hk
          simp only [Finset.mem_Iic] at hk
          exact Nat.pow_le_pow_right hn hk
