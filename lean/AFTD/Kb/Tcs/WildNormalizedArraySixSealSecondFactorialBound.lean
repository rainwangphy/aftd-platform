import AFTD.Prelude
import AFTD.Kb.Tcs.WildNormalizedArrayCommonSixSealsBound
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# wild_normalized_array_six_seal_second_factorial_bound

Topic: graphs   Node: 09484349ac41

Provenance: helper lemma. IN-374 / OP-306, dependence estimates for the weighted partition route to https://arxiv.org/html/2610.22142v1. Elementary matching support consequence of the standard even-cycle decomposition of two disjoint perfect matchings; matching background https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content . Exact experiment9362 audits six saved15 arrays and cyclic9,13,21,27,39,61. No new wild-number bound, sharpness case or research advance is claimed.

For every normalized symmetric idempotent row-injective array on Fin n, let mu(S) count colors outside a six-set S whose matching edges preserve S. The sum over all six-sets of mu(S)*(mu(S)-1) is at most n*(n-1)*floor((n-3)/6). This is a multiplicity bound for six-supports, not a probability bound or an independence claim.
-/

open Finset

theorem wild_normalized_array_six_seal_second_factorial_bound_card_mul_sub_one
    {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) :
    T.card * (T.card - 1) =
      ∑ a ∈ (univ : Finset α), ∑ b ∈ (univ : Finset α),
        if a ≠ b ∧ a ∈ T ∧ b ∈ T then 1 else 0 := by
  have h1 : T.card * (T.card - 1) = ∑ a ∈ T, ∑ b ∈ T.erase a, 1 := by
    have h1' : (∑ a ∈ T, ∑ _b ∈ T.erase a, (1 : ℕ)) = ∑ a ∈ T, (T.card - 1) := by
      apply sum_congr rfl
      intro a ha
      simp [card_erase_of_mem ha]
    rw [h1']
    simp [sum_const]
  have hinner : ∀ a, (∑ b ∈ (univ : Finset α), (if a ≠ b ∧ a ∈ T ∧ b ∈ T then (1 : ℕ) else 0)) =
      if a ∈ T then ∑ b ∈ T.erase a, 1 else 0 := by
    intro a
    split_ifs with ha
    · have hrew : (fun b => (if a ≠ b ∧ a ∈ T ∧ b ∈ T then (1 : ℕ) else 0)) =
                  fun b => (if b ∈ T.erase a then (1 : ℕ) else 0) := by
        ext b
        have : (a ≠ b ∧ a ∈ T ∧ b ∈ T) ↔ b ∈ T.erase a := by
          simp [mem_erase, ha, ne_comm]
        rw [if_congr this rfl rfl]
      rw [hrew, ← sum_filter, filter_mem_eq_of_subset (subset_univ _)]
    · have hrew : (fun b => (if a ≠ b ∧ a ∈ T ∧ b ∈ T then (1 : ℕ) else 0)) = fun _ => 0 := by
        ext b
        have : ¬(a ≠ b ∧ a ∈ T ∧ b ∈ T) := by simp [ha]
        simp [this]
      rw [hrew, sum_const_zero]
  simp_rw [hinner]
  rw [h1]
  rw [← sum_filter, filter_mem_eq_of_subset (subset_univ _)]

theorem wild_normalized_array_six_seal_second_factorial_bound_sum_pairs
    (n : ℕ) (g : Fin n → Fin n → ℕ)
    (hzero : ∀ a, g a a = 0)
    (hbound : ∀ a b, a ≠ b → g a b ≤ (n - 3) / 6) :
    ∑ a ∈ (univ : Finset (Fin n)), ∑ b ∈ (univ : Finset (Fin n)), g a b ≤
      n * (n - 1) * ((n - 3) / 6) := by
  have hinner : ∀ a : Fin n, ∑ b ∈ (univ : Finset (Fin n)), g a b ≤ (n - 1) * ((n - 3) / 6) := by
    intro a
    have hsum := sum_erase_add (univ : Finset (Fin n)) (g a) (mem_univ a)
    rw [hzero a, add_zero] at hsum
    rw [← hsum]
    have hle : ∑ b ∈ (univ : Finset (Fin n)).erase a, g a b ≤
               ∑ _b ∈ (univ : Finset (Fin n)).erase a, ((n - 3) / 6) := by
      apply sum_le_sum
      intro b hb
      exact hbound a b (mem_erase.mp hb).1.symm
    apply hle.trans
    simp [card_erase_of_mem]
  have houter : ∑ a ∈ (univ : Finset (Fin n)), ∑ b ∈ (univ : Finset (Fin n)), g a b ≤
      ∑ _a ∈ (univ : Finset (Fin n)), ((n - 1) * ((n - 3) / 6)) :=
    sum_le_sum (fun a _ => hinner a)
  apply houter.trans
  simp [mul_assoc]

theorem wild_normalized_array_six_seal_second_factorial_bound
    (n : ℕ) (A : Fin n → Fin n → Fin n)
    (hdiag : ∀ x, A x x = x) (hsymm : ∀ x y, A x y = A y x)
    (hinj : ∀ x, Function.Injective (A x)) :
    let mu : Finset (Fin n) → ℕ := fun S =>
      (univ.filter fun i : Fin n => i ∉ S ∧
        ∀ x ∈ S, ∀ y, A x y = i → y ∈ S).card
    ∑ S ∈ (univ : Finset (Fin n)).powersetCard 6, mu S * (mu S - 1) ≤
      n * (n-1) * ((n-3)/6) := by
  intro mu
  let C : Finset (Fin n) → Finset (Fin n) := fun S =>
    univ.filter fun i => i ∉ S ∧ ∀ x ∈ S, ∀ y, A x y = i → y ∈ S
  have hmu : ∀ S, mu S = (C S).card := fun _ => rfl
  have hstep1 : (∑ S ∈ (univ : Finset (Fin n)).powersetCard 6, mu S * (mu S - 1)) =
      ∑ S ∈ (univ : Finset (Fin n)).powersetCard 6,
        ∑ a ∈ (univ : Finset (Fin n)), ∑ b ∈ (univ : Finset (Fin n)),
          if a ≠ b ∧ a ∈ C S ∧ b ∈ C S then 1 else 0 := by
    apply sum_congr rfl
    intro S _
    rw [hmu S, wild_normalized_array_six_seal_second_factorial_bound_card_mul_sub_one (C S)]
  rw [hstep1]
  have hswap : (∑ S ∈ (univ : Finset (Fin n)).powersetCard 6,
        ∑ a ∈ (univ : Finset (Fin n)), ∑ b ∈ (univ : Finset (Fin n)),
          if a ≠ b ∧ a ∈ C S ∧ b ∈ C S then 1 else 0) =
      ∑ a ∈ (univ : Finset (Fin n)), ∑ b ∈ (univ : Finset (Fin n)),
        ∑ S ∈ (univ : Finset (Fin n)).powersetCard 6,
          if a ≠ b ∧ a ∈ C S ∧ b ∈ C S then 1 else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
  rw [hswap]
  let g : Fin n → Fin n → ℕ := fun a b =>
    ∑ S ∈ (univ : Finset (Fin n)).powersetCard 6,
      if a ≠ b ∧ a ∈ C S ∧ b ∈ C S then 1 else 0
  have hzero : ∀ a, g a a = 0 := by
    intro a
    dsimp [g]
    have : (fun S => (if a ≠ a ∧ a ∈ C S ∧ a ∈ C S then (1 : ℕ) else 0)) = fun _ => 0 := by
      ext S
      simp
    rw [this, sum_const_zero]
  have hbound : ∀ a b, a ≠ b → g a b ≤ (n - 3) / 6 := by
    intro a b hab
    dsimp [g]
    have hiff : ∀ S, (a ≠ b ∧ a ∈ C S ∧ b ∈ C S) ↔
        (a ∉ S ∧ b ∉ S ∧ ∀ x ∈ S, ∀ y, A x y = a ∨ A x y = b → y ∈ S) := by
      intro S
      dsimp [C]
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
        refine ⟨ha1, hb1, fun x hx y hy => ?_⟩
        rcases hy with hya | hyb
        · exact ha2 x hx y hya
        · exact hb2 x hx y hyb
      · rintro ⟨ha1, hb1, h⟩
        refine ⟨hab, ⟨ha1, fun x hx y hya => h x hx y (Or.inl hya)⟩,
          ⟨hb1, fun x hx y hyb => h x hx y (Or.inr hyb)⟩⟩
    have hrew : (∑ S ∈ (univ : Finset (Fin n)).powersetCard 6,
        if a ≠ b ∧ a ∈ C S ∧ b ∈ C S then 1 else 0) =
        (((univ : Finset (Fin n)).powersetCard 6).filter fun S =>
          a ∉ S ∧ b ∉ S ∧ ∀ x ∈ S, ∀ y, A x y = a ∨ A x y = b → y ∈ S).card := by
      have h1 : (fun S => (if a ≠ b ∧ a ∈ C S ∧ b ∈ C S then (1 : ℕ) else 0)) =
                fun S => if (a ∉ S ∧ b ∉ S ∧ ∀ x ∈ S, ∀ y, A x y = a ∨ A x y = b → y ∈ S) then 1 else 0 := by
        ext S
        rw [if_congr (hiff S) rfl rfl]
      rw [h1, ← sum_filter]
      simp
    rw [hrew]
    have hb := wild_normalized_array_common_six_seals_bound n A hdiag hsymm hinj a b hab
    have hpos : 0 < 6 := by decide
    rw [Nat.le_div_iff_mul_le hpos]
    linarith
  exact wild_normalized_array_six_seal_second_factorial_bound_sum_pairs n g hzero hbound
