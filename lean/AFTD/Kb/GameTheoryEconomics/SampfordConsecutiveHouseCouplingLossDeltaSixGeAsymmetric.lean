import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordConsecutiveHouseCouplingLossDelta
import AFTD.Kb.GameTheoryEconomics.SampfordConsecutiveHouseCouplingLossDeltaUnfold
import AFTD.Kb.GameTheoryEconomics.SampfordCouplingLoss
import AFTD.Kb.GameTheoryEconomics.SampfordIsCoupling
import AFTD.Kb.GameTheoryEconomics.SampfordProbSubset
import AFTD.Kb.GameTheoryEconomics.SampfordWeight
import AFTD.Kb.GameTheoryEconomics.SampfordTotalWeight
import AFTD.Kb.Tcs.Weight

/-!
# sampford_consecutive_house_coupling_loss_delta_six_ge_asymmetric

Topic: social_choice   Node: 639acd0ad359

Provenance: helper lemma. step towards sampford_balanced_family_not_attain_delta_six

For six parties, the maximal consecutive-house coupling loss Delta_6 is at least 650133/3333400, witnessed by the asymmetric configuration of 4 small parties with vote share 1/400 and 2 large parties with vote share 99/200 at house size h = 200.
-/

namespace sampfordSixAsym

/-- The witness vote-share vector: four small parties at 1/400, two large at 99/200. -/
noncomputable def p6 : Fin 6 → ℝ := fun i => if (i:ℕ) < 4 then 1/400 else 99/200
/-- Residues of `200 * p6`: 1/2 on the small parties, 0 on the large ones. -/
noncomputable def r200 : Fin 6 → ℝ := fun i => if (i:ℕ) < 4 then 1/2 else 0
/-- Residues of `201 * p6`. -/
noncomputable def r201 : Fin 6 → ℝ := fun i => if (i:ℕ) < 4 then 201/400 else 99/200
/-- The four size-3 sets containing both large parties. -/
def B6 : Finset (Finset (Fin 6)) := {({0,4,5} : Finset (Fin 6)), {1,4,5}, {2,4,5}, {3,4,5}}
/-- The six pairs of small parties. -/
def A6 : Finset (Finset (Fin 6)) := {({0,1} : Finset (Fin 6)), {0,2}, {0,3}, {1,2}, {1,3}, {2,3}}
/-- All size-2 subsets of the six parties. -/
def P2 : Finset (Finset (Fin 6)) := Finset.powersetCard 2 (Finset.univ : Finset (Fin 6))
/-- All size-3 subsets of the six parties. -/
def P3 : Finset (Finset (Fin 6)) := Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))

lemma p6_pos : ∀ i, 0 < p6 i := by
  intro i; by_cases h : (i:ℕ) < 4
  · simp only [p6, h, if_true]; norm_num
  · simp only [p6, h, if_false]; norm_num

lemma p6_sum : ∑ i : Fin 6, p6 i = 1 := by
  simp only [p6]; rw [Fin.sum_univ_six]; norm_num

lemma r200_bounds : (∀ i, 0 ≤ r200 i) ∧ (∀ i, r200 i ≤ 1) := by
  constructor <;> intro i <;> by_cases h : (i:ℕ) < 4 <;>
    simp only [r200, h, if_true, if_false] <;> norm_num

lemma r201_bounds : (∀ i, 0 ≤ r201 i) ∧ (∀ i, r201 i ≤ 1) := by
  constructor <;> intro i <;> by_cases h : (i:ℕ) < 4 <;>
    simp only [r201, h, if_true, if_false] <;> norm_num

/-- Sampford weights are nonnegative for residues in `[0,1]`. -/
lemma wnn {n : ℕ} (r : Fin n → ℝ) (h0 : ∀ i, 0 ≤ r i) (h1 : ∀ i, r i ≤ 1)
    (S : Finset (Fin n)) : 0 ≤ sampfordWeight r S := by
  simp only [sampfordWeight]
  exact mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (h1 i)))
    (Finset.prod_nonneg (fun i _ => h0 i))) (Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (h1 i)))

lemma twnn {n : ℕ} (r : Fin n → ℝ) (h0 : ∀ i, 0 ≤ r i) (h1 : ∀ i, r i ≤ 1) (k : ℕ) :
    0 ≤ sampfordTotalWeight r k := by
  simp only [sampfordTotalWeight]
  exact Finset.sum_nonneg (fun S _ => wnn r h0 h1 S)

lemma psnn {n : ℕ} (r : Fin n → ℝ) (h0 : ∀ i, 0 ≤ r i) (h1 : ∀ i, r i ≤ 1)
    (k : ℕ) (S : Finset (Fin n)) : 0 ≤ sampfordProbSubset r k S := by
  simp only [sampfordProbSubset]
  by_cases hk0 : k = 0
  · simp only [hk0, if_true]; split_ifs <;> norm_num
  · by_cases hkn : k = n
    · simp only [hkn, if_true]; split_ifs <;> norm_num
    · simp only [hk0, hkn, if_false]
      split_ifs with hc
      · exact div_nonneg (wnn r h0 h1 S) (twnn r h0 h1 k)
      · exact le_refl 0

lemma nondeg {n : ℕ} (r : Fin n → ℝ) (k : ℕ) (hk0 : k ≠ 0) (hkn : k ≠ n)
    (S : Finset (Fin n)) (hS : S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n))) :
    sampfordProbSubset r k S = sampfordWeight r S / sampfordTotalWeight r k := by
  obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.mp hS
  simp only [sampfordProbSubset, if_neg hk0, if_neg hkn]
  by_cases hc : S.card = k ∧ sampfordTotalWeight r k ≠ 0
  · rw [if_pos hc]
  · rw [if_neg hc]
    have : sampfordTotalWeight r k = 0 := by
      by_contra h; exact hc ⟨hcard, h⟩
    simp [this]

lemma pssum_le_one {n : ℕ} (r : Fin n → ℝ) (k : ℕ) :
    ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), sampfordProbSubset r k S ≤ 1 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [Finset.powersetCard_zero]; simp [sampfordProbSubset]
  · by_cases hkn : k = n
    · have hcardn : (Finset.univ : Finset (Fin n)).card = n := by simp
      have hcard : k = (Finset.univ : Finset (Fin n)).card := by rw [hcardn]; exact hkn
      have hn0 : n ≠ 0 := hkn ▸ hk0
      rw [hcard, Finset.powersetCard_self, Finset.sum_singleton]
      simp [sampfordProbSubset, hcardn, hn0]
    · rw [Finset.sum_congr rfl (fun S hS => nondeg r k hk0 hkn S hS), ← Finset.sum_div,
        show (∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), sampfordWeight r S)
          = sampfordTotalWeight r k from rfl]
      by_cases hTW : sampfordTotalWeight r k = 0
      · simp [hTW]
      · rw [div_self hTW]

lemma pssum_eq_one {n : ℕ} (r : Fin n → ℝ) (k : ℕ)
    (hTW : sampfordTotalWeight r k ≠ 0) :
    ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), sampfordProbSubset r k S = 1 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [Finset.powersetCard_zero]; simp [sampfordProbSubset]
  · by_cases hkn : k = n
    · have hcardn : (Finset.univ : Finset (Fin n)).card = n := by simp
      have hcard : k = (Finset.univ : Finset (Fin n)).card := by rw [hcardn]; exact hkn
      have hn0 : n ≠ 0 := hkn ▸ hk0
      rw [hcard, Finset.powersetCard_self, Finset.sum_singleton]
      simp [sampfordProbSubset, hcardn, hn0]
    · rw [Finset.sum_congr rfl (fun S hS => nondeg r k hk0 hkn S hS), ← Finset.sum_div,
        show (∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), sampfordWeight r S)
          = sampfordTotalWeight r k from rfl]
      rw [div_self hTW]

lemma loss_nonneg {n : ℕ} (p : Fin n → ℝ) (h : ℕ) (prob : Finset (Fin n) → Finset (Fin n) → ℝ)
    (hc : sampfordIsCoupling p h prob) : 0 ≤ sampfordCouplingLoss p h prob := by
  simp only [sampfordCouplingLoss]
  apply Finset.sum_nonneg; intro S _
  apply Finset.sum_nonneg; intro T _
  split_ifs with hbad
  · exact hc.1 S T
  · exact le_refl 0

lemma loss_le_one {n : ℕ} (p : Fin n → ℝ) (h : ℕ) (prob : Finset (Fin n) → Finset (Fin n) → ℝ)
    (hc : sampfordIsCoupling p h prob) : sampfordCouplingLoss p h prob ≤ 1 := by
  classical
  have h2 : ∑ S ∈ Finset.powersetCard (h - ∑ i, ⌊↑h * p i⌋₊) (Finset.univ : Finset (Fin n)),
      ∑ T ∈ Finset.powersetCard (h + 1 - ∑ i, ⌊(↑h + 1) * p i⌋₊) (Finset.univ : Finset (Fin n)),
        prob S T ≤ 1 := by
    rw [Finset.sum_congr rfl (fun S hS => hc.2.1 S hS)]
    exact pssum_le_one _ _
  simp only [sampfordCouplingLoss]
  refine le_trans ?_ h2
  apply Finset.sum_le_sum; intro S _
  apply Finset.sum_le_sum; intro T _
  split_ifs with hbad
  · exact le_refl _
  · exact hc.1 S T

/-- The inner infimum of coupling losses is at most 1. -/
lemma inner_le_one {n : ℕ} (p : Fin n → ℝ) (h : ℕ) :
    sInf {L | ∃ prob, sampfordIsCoupling p h prob ∧ L = sampfordCouplingLoss p h prob} ≤ 1 := by
  by_cases hne : (Set.Nonempty {L : ℝ | ∃ prob, sampfordIsCoupling p h prob ∧
      L = sampfordCouplingLoss p h prob})
  · obtain ⟨L, prob, hc, rfl⟩ := hne
    refine le_trans (csInf_le ⟨0, ?_⟩ ⟨prob, hc, rfl⟩) (loss_le_one p h prob hc)
    rintro b ⟨prob', hc', rfl⟩
    exact loss_nonneg p h prob' hc'
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]; norm_num

lemma floor200 (i : Fin 6) : ⌊((200:ℕ):ℝ) * p6 i⌋₊ = (if (i:ℕ) < 4 then 0 else 99) := by
  by_cases h : (i:ℕ) < 4
  · simp only [p6, h, if_true]; norm_num
  · simp only [p6, h, if_false]; norm_num

lemma floor201 (i : Fin 6) : ⌊(((200:ℕ):ℝ) + 1) * p6 i⌋₊ = (if (i:ℕ) < 4 then 0 else 99) := by
  by_cases h : (i:ℕ) < 4
  · simp only [p6, h, if_true]; norm_num
  · simp only [p6, h, if_false]; norm_num

lemma sumfloor200 : (∑ i : Fin 6, ⌊((200:ℕ):ℝ) * p6 i⌋₊) = 198 := by
  simp only [floor200]; decide

lemma sumfloor201 : (∑ i : Fin 6, ⌊(((200:ℕ):ℝ) + 1) * p6 i⌋₊) = 198 := by
  simp only [floor201]; decide

lemma res200 (i : Fin 6) : ((200:ℕ):ℝ) * p6 i - ⌊((200:ℕ):ℝ) * p6 i⌋₊ = r200 i := by
  by_cases h : (i:ℕ) < 4
  · simp only [p6, r200, h, if_true]; norm_num
  · simp only [p6, r200, h, if_false]; norm_num

lemma res201 (i : Fin 6) : (((200:ℕ):ℝ) + 1) * p6 i - ⌊(((200:ℕ):ℝ) + 1) * p6 i⌋₊ = r201 i := by
  by_cases h : (i:ℕ) < 4
  · simp only [p6, r201, h, if_true]; norm_num
  · simp only [p6, r201, h, if_false]; norm_num

/-- A party loses a seat in going from house 200 to 201 exactly when `S ⊄ T`. -/
lemma bad_iff (S T : Finset (Fin 6)) :
    (∃ i : Fin 6, ((if (i:ℕ) < 4 then (0:ℕ) else 99) + (if i ∈ T then 1 else 0))
        < ((if (i:ℕ) < 4 then (0:ℕ) else 99) + (if i ∈ S then 1 else 0))) ↔ ¬ S ⊆ T := by
  have key : ∀ i : Fin 6, (((if (i:ℕ) < 4 then (0:ℕ) else 99) + (if i ∈ T then 1 else 0))
        < ((if (i:ℕ) < 4 then (0:ℕ) else 99) + (if i ∈ S then 1 else 0))) ↔ (i ∈ S ∧ i ∉ T) := by
    intro i
    rw [Nat.add_lt_add_iff_left]
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp [hiS, hiT]
  simp only [key, Finset.not_subset]

/-- The coupling loss at the witness configuration is the total mass of the non-subset pairs. -/
lemma loss200 (prob : Finset (Fin 6) → Finset (Fin 6) → ℝ) :
    sampfordCouplingLoss p6 200 prob
      = ∑ S ∈ P2, ∑ T ∈ P3, (if ¬ (S ⊆ T) then prob S T else 0) := by
  simp only [sampfordCouplingLoss]
  rw [sumfloor200, sumfloor201]
  simp only [floor200, floor201, bad_iff, P2, P3]

/-- Unfolding the coupling condition at the witness configuration. -/
lemma isCoupling_unfold (prob : Finset (Fin 6) → Finset (Fin 6) → ℝ) :
    sampfordIsCoupling p6 200 prob ↔
      ((∀ S T, 0 ≤ prob S T) ∧
        (∀ S ∈ P2, ∑ T ∈ P3, prob S T = sampfordProbSubset r200 2 S) ∧
        (∀ T ∈ P3, ∑ S ∈ P2, prob S T = sampfordProbSubset r201 3 T)) := by
  simp only [sampfordIsCoupling]
  have h1 : (fun i => ((200:ℕ):ℝ) * p6 i - ↑⌊((200:ℕ):ℝ) * p6 i⌋₊) = r200 := by
    funext i; exact res200 i
  have h2 : (fun i => (((200:ℕ):ℝ) + 1) * p6 i - ↑⌊(((200:ℕ):ℝ) + 1) * p6 i⌋₊) = r201 := by
    funext i; exact res201 i
  rw [sumfloor200, sumfloor201, h1, h2]
  norm_num [P2, P3]

/-- Clearing denominators in a Sampford weight with residues `u/D` and `1 - r = w/D`. -/
lemma weight_cast_gen {n : ℕ} (D : ℤ) (u w : Fin n → ℤ) (r : Fin n → ℝ)
    (hr : ∀ i, r i = (u i : ℝ) / (D : ℝ)) (hr' : ∀ i, 1 - r i = (w i : ℝ) / (D : ℝ))
    (S : Finset (Fin n)) :
    sampfordWeight r S
      = (((∑ i ∈ S, w i) * (∏ i ∈ S, u i) * (∏ i ∈ Finset.univ \ S, w i) : ℤ) : ℝ) / (D : ℝ)^(n+1) := by
  have hcard : S.card + (Finset.univ \ S).card = n := by
    have h : S.card ≤ n := by simpa using Finset.card_le_univ S
    rw [Finset.card_sdiff]; simp; omega
  have hs : (∑ i ∈ S, (1 - r i)) = ((∑ i ∈ S, w i : ℤ) : ℝ) / (D:ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hr' i), ← Finset.sum_div, Int.cast_sum]
  have hp1 : (∏ i ∈ S, r i) = ((∏ i ∈ S, u i : ℤ) : ℝ) / (D:ℝ)^(S.card) := by
    rw [Finset.prod_congr rfl (fun i _ => hr i), Finset.prod_div_distrib, Finset.prod_const,
      Int.cast_prod]
  have hp2 : (∏ i ∈ Finset.univ \ S, (1 - r i))
      = ((∏ i ∈ Finset.univ \ S, w i : ℤ) : ℝ) / (D:ℝ)^((Finset.univ \ S).card) := by
    rw [Finset.prod_congr rfl (fun i _ => hr' i), Finset.prod_div_distrib, Finset.prod_const,
      Int.cast_prod]
  rw [sampfordWeight, hs, hp1, hp2, Int.cast_mul, Int.cast_mul]
  have hp : (D:ℝ) * (D:ℝ) ^ S.card * (D:ℝ) ^ (Finset.univ \ S).card = (D:ℝ)^(n+1) := by
    have h2 : (D:ℝ) ^ (1 + S.card + (Finset.univ \ S).card) = (D:ℝ)^(n+1) := by
      rw [show 1 + S.card + (Finset.univ \ S).card = n + 1 by omega]
    rw [pow_add, pow_add, pow_one] at h2
    exact h2
  rw [div_mul_div_comm, div_mul_div_comm, hp]

/-- Integer numerators of `r201`. -/
def vz : Fin 6 → ℤ := fun i => if (i:ℕ) < 4 then 201 else 198
/-- Integer numerators of `1 - r201`. -/
def mz : Fin 6 → ℤ := fun i => if (i:ℕ) < 4 then 199 else 202
/-- The scaled Sampford weight of `S` at the house-201 residues. -/
def wzf (S : Finset (Fin 6)) : ℤ :=
  (∑ i ∈ S, mz i) * (∏ i ∈ S, vz i) * (∏ i ∈ Finset.univ \ S, mz i)

lemma r201_eq (i : Fin 6) : r201 i = (vz i : ℝ)/400 := by
  by_cases h : (i:ℕ) < 4
  · simp only [r201, vz, h, if_true]; norm_num
  · simp only [r201, vz, h, if_false]; norm_num

lemma one_sub_r201_eq (i : Fin 6) : 1 - r201 i = (mz i : ℝ)/400 := by
  by_cases h : (i:ℕ) < 4
  · simp only [r201, mz, h, if_true]; norm_num
  · simp only [r201, mz, h, if_false]; norm_num

lemma weight201_cast (S : Finset (Fin 6)) : sampfordWeight r201 S = (wzf S : ℝ)/400^7 := by
  have h := weight_cast_gen 400 vz mz r201 r201_eq one_sub_r201_eq S
  simpa [wzf] using h

lemma WZ_total :
    (∑ S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6)), wzf S) = 767976959712009600 := by
  decide

lemma hTW201_val : sampfordTotalWeight r201 3 = (767976959712009600 : ℝ)/400^7 := by
  rw [sampfordTotalWeight,
    Finset.sum_congr rfl (fun S (_ : S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))) =>
      weight201_cast S)]
  rw [← Finset.sum_div, ← Int.cast_sum, WZ_total]
  norm_num

lemma hTW201 : sampfordTotalWeight r201 3 ≠ 0 := by rw [hTW201_val]; norm_num

/-- Integer numerators of `r200`. -/
def u2 : Fin 6 → ℤ := fun i => if (i:ℕ) < 4 then 1 else 0
/-- Integer numerators of `1 - r200`. -/
def w2 : Fin 6 → ℤ := fun i => if (i:ℕ) < 4 then 1 else 2

lemma r200_eq (i : Fin 6) : r200 i = (u2 i : ℝ)/2 := by
  by_cases h : (i:ℕ) < 4
  · simp only [r200, u2, h, if_true]; norm_num
  · simp only [r200, u2, h, if_false]; norm_num

lemma one_sub_r200_eq (i : Fin 6) : 1 - r200 i = (w2 i : ℝ)/2 := by
  by_cases h : (i:ℕ) < 4
  · simp only [r200, w2, h, if_true]; norm_num
  · simp only [r200, w2, h, if_false]; norm_num

lemma weight200_cast (S : Finset (Fin 6)) :
    sampfordWeight r200 S
      = (((∑ i ∈ S, w2 i) * (∏ i ∈ S, u2 i) * (∏ i ∈ Finset.univ \ S, w2 i) : ℤ) : ℝ)/2^7 := by
  have h := weight_cast_gen 2 u2 w2 r200 r200_eq one_sub_r200_eq S
  simpa using h

lemma WZ200 :
    (∑ S ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 6)),
      (∑ i ∈ S, w2 i) * (∏ i ∈ S, u2 i) * (∏ i ∈ Finset.univ \ S, w2 i)) = 48 := by
  decide

lemma hTW200_val : sampfordTotalWeight r200 2 = (48 : ℝ)/2^7 := by
  rw [sampfordTotalWeight,
    Finset.sum_congr rfl (fun S (_ : S ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 6))) =>
      weight200_cast S)]
  rw [← Finset.sum_div, ← Int.cast_sum, WZ200]
  norm_num

lemma hTW200 : sampfordTotalWeight r200 2 ≠ 0 := by rw [hTW200_val]; norm_num

/-- The Sampford probability at house 201 of a size-3 set, cleared of denominators. -/
lemma prob201_val (T : Finset (Fin 6)) (hT : T ∈ P3) :
    sampfordProbSubset r201 3 T = (wzf T : ℝ)/767976959712009600 := by
  rw [nondeg r201 3 (by norm_num) (by norm_num) T hT, weight201_cast T, hTW201_val]
  exact div_div_div_cancel_right₀ (by norm_num) _ _

lemma r200_four : r200 (4 : Fin 6) = 0 := by simp [r200]
lemma r200_five : r200 (5 : Fin 6) = 0 := by simp [r200]

lemma weight200_zero (S : Finset (Fin 6)) (h : (4:Fin 6) ∈ S ∨ (5:Fin 6) ∈ S) :
    sampfordWeight r200 S = 0 := by
  have hz : (∏ i ∈ S, r200 i) = 0 := by
    rcases h with h | h
    · exact Finset.prod_eq_zero h r200_four
    · exact Finset.prod_eq_zero h r200_five
  simp only [sampfordWeight, hz, mul_zero, zero_mul]

lemma prob200_zero (S : Finset (Fin 6)) (h : (4:Fin 6) ∈ S ∨ (5:Fin 6) ∈ S) :
    sampfordProbSubset r200 2 S = 0 := by
  simp only [sampfordProbSubset]
  rw [if_neg (by norm_num : (2:ℕ) ≠ 0), if_neg (by norm_num : (2:ℕ) ≠ 6)]
  split_ifs with hc
  · rw [weight200_zero S h]; simp
  · rfl

lemma A6_sub : A6 ⊆ P2 := by decide

lemma B6_sub : ∀ T ∈ B6, T ∈ P3 := by
  intro T hT
  simp only [B6, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl <;> decide

lemma notA6_large : ∀ S ∈ P2, S ∉ A6 → ((4:Fin 6) ∈ S ∨ (5:Fin 6) ∈ S) := by decide

lemma A6_bad : ∀ S ∈ A6, ∀ T ∈ B6, ¬ S ⊆ T := by decide

lemma B6_sum : (∑ T ∈ B6, wzf T) = 149783153761459152 := by decide

lemma sumP2 : (∑ i ∈ P2, sampfordProbSubset r200 2 i) = 1 := pssum_eq_one r200 2 hTW200
lemma sumP3 : (∑ i ∈ P3, sampfordProbSubset r201 3 i) = 1 := pssum_eq_one r201 3 hTW201

/-- Total Sampford mass at house 201 of the four triples containing both large parties. -/
lemma prob201_sum_B : (∑ T ∈ B6, sampfordProbSubset r201 3 T) = 650133/3333400 := by
  rw [Finset.sum_congr rfl (fun T hT => prob201_val T (B6_sub T hT))]
  rw [← Finset.sum_div, ← Int.cast_sum, B6_sum]
  norm_num

/-- A valid coupling exists at the witness configuration (the product coupling). -/
lemma coupling_exists : ∃ prob, sampfordIsCoupling p6 200 prob := by
  refine ⟨fun S T => sampfordProbSubset r200 2 S * sampfordProbSubset r201 3 T, ?_⟩
  rw [isCoupling_unfold]
  refine ⟨fun S T => mul_nonneg (psnn r200 r200_bounds.1 r200_bounds.2 2 S)
    (psnn r201 r201_bounds.1 r201_bounds.2 3 T), ?_, ?_⟩
  · intro S _
    rw [← Finset.mul_sum, sumP3, mul_one]
  · intro T _
    rw [← Finset.sum_mul, sumP2, one_mul]

/-- The key lower bound: every valid coupling at the witness configuration has loss at least
`650133/3333400`. -/
lemma key_bound (prob : Finset (Fin 6) → Finset (Fin 6) → ℝ)
    (hc : sampfordIsCoupling p6 200 prob) :
    (650133:ℝ)/3333400 ≤ sampfordCouplingLoss p6 200 prob := by
  classical
  obtain ⟨hnn, hrow, hcol⟩ := (isCoupling_unfold prob).mp hc
  rw [loss200]
  have rowzero : ∀ S ∈ P2, S ∉ A6 → ∑ T ∈ B6, prob S T = 0 := by
    intro S hS hS'
    have hbig : ∑ T ∈ P3, prob S T = 0 := by
      rw [hrow S hS, prob200_zero S (notA6_large S hS hS')]
    have hle : ∑ T ∈ B6, prob S T ≤ ∑ T ∈ P3, prob S T :=
      Finset.sum_le_sum_of_subset_of_nonneg B6_sub (fun T _ _ => hnn S T)
    have hnn' : 0 ≤ ∑ T ∈ B6, prob S T := Finset.sum_nonneg (fun T _ => hnn S T)
    linarith
  have key : ∑ S ∈ A6, ∑ T ∈ B6, prob S T = (650133:ℝ)/3333400 := by
    rw [Finset.sum_subset A6_sub rowzero, Finset.sum_comm,
      Finset.sum_congr rfl (fun T hT => hcol T (B6_sub T hT))]
    exact prob201_sum_B
  have step1 : ∑ S ∈ A6, ∑ T ∈ B6, prob S T
      ≤ ∑ S ∈ A6, ∑ T ∈ P3, (if ¬ (S ⊆ T) then prob S T else 0) := by
    apply Finset.sum_le_sum
    intro S hS
    have hT : ∀ T ∈ B6, prob S T = (if ¬ (S ⊆ T) then prob S T else 0) := by
      intro T hT
      rw [if_pos (A6_bad S hS T hT)]
    rw [Finset.sum_congr rfl hT]
    exact Finset.sum_le_sum_of_subset_of_nonneg B6_sub (fun T _ _ => by
      by_cases h : ¬ (S ⊆ T)
      · rw [if_pos h]; exact hnn S T
      · rw [if_neg h])
  have step2 : ∑ S ∈ A6, ∑ T ∈ P3, (if ¬ (S ⊆ T) then prob S T else 0)
      ≤ ∑ S ∈ P2, ∑ T ∈ P3, (if ¬ (S ⊆ T) then prob S T else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg A6_sub
      (fun S _ _ => Finset.sum_nonneg (fun T _ => by
        by_cases h : ¬ (S ⊆ T)
        · rw [if_pos h]; exact hnn S T
        · rw [if_neg h]))
  rw [← key]
  exact le_trans step1 step2

end sampfordSixAsym

/-- For six parties, the maximal consecutive-house coupling loss Delta_6 is at least 650133/3333400, witnessed by the asymmetric configuration of 4 small parties with vote share 1/400 and 2 large parties with vote share 99/200 at house size h = 200. -/
theorem sampford_consecutive_house_coupling_loss_delta_six_ge_asymmetric :
    (650133 : ℝ) / 3333400 ≤ sampfordConsecutiveHouseCouplingLossDelta 6 := by
  classical
  obtain ⟨prob0, hc0⟩ := sampfordSixAsym.coupling_exists
  have hmem : sInf {L | ∃ prob, sampfordIsCoupling sampfordSixAsym.p6 200 prob ∧
      L = sampfordCouplingLoss sampfordSixAsym.p6 200 prob} ∈
      {v : ℝ | ∃ (p : Fin 6 → ℝ) (h : ℕ), (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ 1 ≤ h ∧
        v = sInf {L | ∃ prob, sampfordIsCoupling p h prob ∧ L = sampfordCouplingLoss p h prob}} :=
    ⟨sampfordSixAsym.p6, 200, sampfordSixAsym.p6_pos, sampfordSixAsym.p6_sum,
      by norm_num, rfl⟩
  have hbdd' : BddAbove {v : ℝ | ∃ (p : Fin 6 → ℝ) (h : ℕ), (∀ i, 0 < p i) ∧
      ∑ i, p i = 1 ∧ 1 ≤ h ∧
      v = sInf {L | ∃ prob, sampfordIsCoupling p h prob ∧ L = sampfordCouplingLoss p h prob}} := by
    refine ⟨1, ?_⟩
    rintro v ⟨p, h, hp, hs, hh, rfl⟩
    exact sampfordSixAsym.inner_le_one p h
  rw [sampford_consecutive_house_coupling_loss_delta_unfold]
  refine le_trans ?_ (le_csSup hbdd' hmem)
  refine le_csInf ⟨sampfordCouplingLoss sampfordSixAsym.p6 200 prob0, prob0, hc0, rfl⟩ ?_
  rintro L ⟨prob, hc, rfl⟩
  exact sampfordSixAsym.key_bound prob hc
