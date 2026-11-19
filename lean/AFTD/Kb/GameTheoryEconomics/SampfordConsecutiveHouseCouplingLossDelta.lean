import AFTD.Prelude

/-!
# sampfordConsecutiveHouseCouplingLossDelta

Topic: social_choice   Node: 9ac661edb8bb

Provenance: formalization of a published result. Source: Correa et al., arXiv:2405.03687, Section 3.3 and Appendix A

The maximal consecutive-house coupling loss Delta_n for Sampford apportionment on n parties, defined as the supremum over all positive vote-share vectors p on n parties (with p_i > 0 and sum p_i = 1) and house sizes h >= 1, of the infimum over all valid couplings of the Sampford apportionment seat distributions at house sizes h and h + 1 of the probability that some party i receives strictly fewer seats at house h + 1 than at house h. At each house size h, party i receives its lower quota floor(h p_i) plus an indicator of whether i is in the subset S of size k = h - sum_j floor(h p_j) drawn according to Sampford's rejective sampling law on the fractional residues r_j = h p_j - floor(h p_j).
-/

open Classical in
/-- Maximal consecutive-house coupling loss Delta_n for Sampford apportionment on n parties. -/
noncomputable def sampfordConsecutiveHouseCouplingLossDelta (n : ℕ) : ℝ :=
  let weight (r : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
    (∑ i ∈ S, (1 - r i)) * (∏ i ∈ S, r i) * (∏ i ∈ (Finset.univ \ S), (1 - r i))
  let totalWeight (r : Fin n → ℝ) (k : ℕ) : ℝ :=
    ∑ S ∈ Finset.powersetCard k Finset.univ, weight r S
  let probSubset (r : Fin n → ℝ) (k : ℕ) (S : Finset (Fin n)) : ℝ :=
    if k = 0 then (if S = ∅ then 1 else 0)
    else if k = n then (if S = Finset.univ then 1 else 0)
    else if S.card = k ∧ totalWeight r k ≠ 0 then weight r S / totalWeight r k
    else 0
  let isCoupling (p : Fin n → ℝ) (h : ℕ) (prob : Finset (Fin n) → Finset (Fin n) → ℝ) : Prop :=
    let l (i : Fin n) := Nat.floor (h * p i)
    let r (i : Fin n) := h * p i - l i
    let k := h - ∑ i, l i
    let l' (i : Fin n) := Nat.floor ((h + 1) * p i)
    let r' (i : Fin n) := (h + 1) * p i - l' i
    let k' := (h + 1) - ∑ i, l' i
    (∀ S T, 0 ≤ prob S T) ∧
    (∀ S ∈ Finset.powersetCard k Finset.univ,
      ∑ T ∈ Finset.powersetCard k' Finset.univ, prob S T = probSubset r k S) ∧
    (∀ T ∈ Finset.powersetCard k' Finset.univ,
      ∑ S ∈ Finset.powersetCard k Finset.univ, prob S T = probSubset r' k' T)
  let loss (p : Fin n → ℝ) (h : ℕ) (prob : Finset (Fin n) → Finset (Fin n) → ℝ) : ℝ :=
    let l (i : Fin n) := Nat.floor (h * p i)
    let k := h - ∑ i, l i
    let l' (i : Fin n) := Nat.floor ((h + 1) * p i)
    let k' := (h + 1) - ∑ i, l' i
    ∑ S ∈ Finset.powersetCard k Finset.univ,
      ∑ T ∈ Finset.powersetCard k' Finset.univ,
        if ∃ i : Fin n, l' i + (if i ∈ T then 1 else 0) < l i + (if i ∈ S then 1 else 0)
        then prob S T else 0
  sSup { v | ∃ (p : Fin n → ℝ) (h : ℕ),
    (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ 1 ≤ h ∧
    v = sInf { L | ∃ prob, isCoupling p h prob ∧ L = loss p h prob } }
