import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoupling
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceState
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCardFilter
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCardNe

/-!
# persuasion_slice_scheme_sender_utility

Topic: mechanism_design   Node: 453098f39d94

The slice scheme gives the sender C(2m+1,m) - C(2m-1,m): a coordinate is recommended 1 iff its m-subset meets the two paired states.
-/

open Finset in
/-- `m`-subsets meeting a 2-set: `C(2m+1,m) - C(2m-1,m)` of them. -/
lemma persuasion_slice_card_meet (m : ℕ) (s t : Fin (2 * m + 1)) (hst : s ≠ t) :
    ((powersetCard m Finset.univ).filter (fun i => s ∈ i ∨ t ∈ i)).card + (2 * m - 1).choose m
      = (2 * m + 1).choose m := by
  have h := card_filter_add_card_filter_not (s := powersetCard m (Finset.univ : Finset (Fin (2 * m + 1))))
    (p := fun i => s ∈ i ∨ t ∈ i)
  rw [card_powersetCard, card_univ, Fintype.card_fin] at h
  have e : (powersetCard m (Finset.univ : Finset (Fin (2 * m + 1)))).filter (fun i => ¬ (s ∈ i ∨ t ∈ i))
      = powersetCard m (Finset.univ \ {s, t}) := by
    ext i
    simp only [Finset.mem_filter, mem_powersetCard, Finset.subset_univ, true_and, not_or]
    constructor
    · rintro ⟨hc, hs, ht⟩
      refine ⟨fun x hx => ?_, hc⟩
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and]
      rintro (rfl | rfl) <;> contradiction
    · rintro ⟨hsub, hc⟩
      refine ⟨hc, fun hs => ?_, fun ht => ?_⟩
      · have := hsub hs; simp at this
      · have := hsub ht; simp at this
  rw [e, card_powersetCard, card_sdiff_of_subset (Finset.subset_univ _), card_univ, Fintype.card_fin,
    card_pair hst, show 2 * m + 1 - 2 = 2 * m - 1 by omega] at h
  omega

open Finset in
/-- Pushing a double sum through the coupling. -/
lemma persuasion_slice_coupling_sum (m : ℕ)
    (g : (persuasion_slice_coord m → Bool) → (persuasion_slice_coord m → Bool) → ℝ) :
    ∑ x, ∑ y, persuasion_slice_coupling m x y * g x y =
      ∑ s, ∑ t, if s ≠ t then 1 / ((2 * m + 1 : ℝ) * (2 * m)) *
        g (persuasion_slice_state m s) (persuasion_slice_state m t) else 0 := by
  classical
  set c : ℝ := 1 / ((2 * m + 1 : ℝ) * (2 * m))
  set v := persuasion_slice_state m
  let F : Fin (2 * m + 1) → Fin (2 * m + 1) → (persuasion_slice_coord m → Bool) →
      (persuasion_slice_coord m → Bool) → ℝ := fun s t x y =>
    if s ≠ t ∧ v s = x ∧ v t = y then c * g x y else 0
  have step : ∀ x y, persuasion_slice_coupling m x y * g x y = ∑ s, ∑ t, F s t x y := by
    intro x y
    unfold persuasion_slice_coupling
    rw [sum_mul]
    apply sum_congr rfl; intro s _
    rw [sum_mul]
    apply sum_congr rfl; intro t _
    simp only [F, ite_mul, zero_mul]
    rfl
  have inner : ∀ s t, ∑ x, ∑ y, F s t x y =
      if s ≠ t then c * g (v s) (v t) else 0 := by
    intro s t
    by_cases h1 : s ≠ t
    · have e : ∀ x y, F s t x y = if v s = x then (if v t = y then c * g x y else 0) else 0 := by
        intro x y
        simp only [F]
        by_cases h2 : v s = x <;> by_cases h3 : v t = y <;> simp [h1, h2, h3]
      simp only [e]
      rw [if_pos h1]
      have e2 : ∀ x, (∑ y, if v s = x then (if v t = y then c * g x y else 0) else 0) =
          if v s = x then (∑ y, if v t = y then c * g x y else 0) else 0 := by
        intro x; split_ifs <;> simp
      simp only [e2]
      rw [sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      rw [sum_ite_eq]
      simp
    · have e : ∀ x y, F s t x y = 0 := by
        intro x y; simp only [F]; simp [h1]
      simp [e, h1]
  calc ∑ x, ∑ y, persuasion_slice_coupling m x y * g x y
      = ∑ p : (persuasion_slice_coord m → Bool) × (persuasion_slice_coord m → Bool),
          ∑ r : Fin (2 * m + 1) × Fin (2 * m + 1), F r.1 r.2 p.1 p.2 := by
        rw [← Fintype.sum_prod_type']
        apply sum_congr rfl; intro p _
        rw [step, ← Fintype.sum_prod_type']
    _ = ∑ r : Fin (2 * m + 1) × Fin (2 * m + 1),
          ∑ p : (persuasion_slice_coord m → Bool) × (persuasion_slice_coord m → Bool),
            F r.1 r.2 p.1 p.2 := sum_comm
    _ = ∑ r : Fin (2 * m + 1) × Fin (2 * m + 1),
          (if r.1 ≠ r.2 then c * g (v r.1) (v r.2) else 0) :=
        sum_congr rfl (fun r _ => by rw [← inner, ← Fintype.sum_prod_type'])
    _ = _ := Fintype.sum_prod_type' (fun s t => if s ≠ t then c * g (v s) (v t) else 0)

open Finset in
/-- The slice scheme gives the sender `C(2m+1,m) - C(2m-1,m)`: a coordinate is recommended `1` iff its `m`-subset meets the two paired states. -/
lemma persuasion_slice_scheme_sender_utility (m : ℕ) (hm : 1 ≤ m) :
    persuasion_sender_utility (persuasion_slice_scheme m) =
      ((2 * m + 1).choose m : ℝ) - (2 * m - 1).choose m := by
  classical
  set N : ℝ := ((2 * m + 1).choose m : ℝ) - (2 * m - 1).choose m
  unfold persuasion_slice_scheme
  rw [persuasion_pair_or_sender_utility, persuasion_slice_coupling_sum]
  have hcnt : ∀ s t : Fin (2 * m + 1), s ≠ t →
      ((Finset.univ.filter (fun i : persuasion_slice_coord m => (persuasion_slice_state m s i ||
        persuasion_slice_state m t i) = true)).card : ℝ) = N := by
    intro s t hst
    have e : (Finset.univ.filter (fun i : persuasion_slice_coord m => (persuasion_slice_state m s i ||
        persuasion_slice_state m t i) = true)) =
        Finset.univ.filter (fun i : persuasion_slice_coord m => (fun j => s ∈ j ∨ t ∈ j) i.1) := by
      ext i; simp [persuasion_slice_state]
    rw [e, persuasion_slice_card_filter m (fun j => s ∈ j ∨ t ∈ j)]
    have := persuasion_slice_card_meet m s t hst
    simp only [N]
    rw [← this]
    push_cast
    ring
  have e2 : ∀ s, (∑ t, if s ≠ t then 1 / ((2 * m + 1 : ℝ) * (2 * m)) *
      ((Finset.univ.filter (fun i : persuasion_slice_coord m => (persuasion_slice_state m s i ||
        persuasion_slice_state m t i) = true)).card : ℝ) else 0) =
      2 * m * (1 / ((2 * m + 1 : ℝ) * (2 * m)) * N) := by
    intro s
    rw [← sum_filter]
    rw [sum_congr rfl (fun t ht => by rw [hcnt s t (Finset.mem_filter.mp ht).2]), Finset.sum_const,
      persuasion_slice_card_ne, nsmul_eq_mul]
    push_cast; ring
  rw [sum_congr rfl (fun s _ => e2 s), Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  push_cast
  field_simp
