import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordProbSubset

/-!
# sampfordIsCoupling

Topic: social_choice   Node: 35effa860450

Provenance: helper lemma. step towards sampford_consecutive_house_coupling_loss_delta_four

prob is a valid coupling of the Sampford apportionments at house sizes h and h+1 for the vote-share vector p: it is nonnegative and its marginals are the Sampford laws on size-k subsets given the residues of h*p and on size-k' subsets given the residues of (h+1)*p.
-/

open Classical in
/-- Validity of a coupling of the two consecutive-house Sampford apportionments. -/
noncomputable def sampfordIsCoupling {n : ℕ} (p : Fin n → ℝ) (h : ℕ) (prob : Finset (Fin n) → Finset (Fin n) → ℝ) : Prop :=
  let l (i : Fin n) := Nat.floor (h * p i)
  let r (i : Fin n) := h * p i - l i
  let k := h - ∑ i, l i
  let l' (i : Fin n) := Nat.floor ((h + 1) * p i)
  let r' (i : Fin n) := (h + 1) * p i - l' i
  let k' := (h + 1) - ∑ i, l' i
  (∀ S T, 0 ≤ prob S T) ∧
  (∀ S ∈ Finset.powersetCard k Finset.univ,
    ∑ T ∈ Finset.powersetCard k' Finset.univ, prob S T = sampfordProbSubset r k S) ∧
  (∀ T ∈ Finset.powersetCard k' Finset.univ,
    ∑ S ∈ Finset.powersetCard k Finset.univ, prob S T = sampfordProbSubset r' k' T)
