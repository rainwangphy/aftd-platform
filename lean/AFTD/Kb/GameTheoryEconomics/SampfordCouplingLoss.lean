import AFTD.Prelude

/-!
# sampfordCouplingLoss

Topic: social_choice   Node: bb9d9a9b7b04

Provenance: helper lemma. step towards sampford_consecutive_house_coupling_loss_delta_four

The coupling loss: the total probability, under the coupling prob, of those pairs (S,T) of seat-assignment subsets for which some party i receives strictly fewer seats at house size h+1 than at house size h.
-/

open Classical in
/-- Probability, under a coupling, that some party loses a seat when the house grows from h to h+1. -/
noncomputable def sampfordCouplingLoss {n : ℕ} (p : Fin n → ℝ) (h : ℕ) (prob : Finset (Fin n) → Finset (Fin n) → ℝ) : ℝ :=
  let l (i : Fin n) := Nat.floor (h * p i)
  let k := h - ∑ i, l i
  let l' (i : Fin n) := Nat.floor ((h + 1) * p i)
  let k' := (h + 1) - ∑ i, l' i
  ∑ S ∈ Finset.powersetCard k Finset.univ,
    ∑ T ∈ Finset.powersetCard k' Finset.univ,
      if ∃ i : Fin n, l' i + (if i ∈ T then 1 else 0) < l i + (if i ∈ S then 1 else 0)
      then prob S T else 0
