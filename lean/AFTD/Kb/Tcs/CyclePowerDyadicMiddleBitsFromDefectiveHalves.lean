import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingDefectiveHalves
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalvesEliminateMiddle
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_middle_bits_from_defective_halves

Topic: combinatorics   Node: 52b323be55a8

Provenance: helper lemma. Conditional assembly of the middle-bit statement from the defective half-model ladder for RT-1.

If both phase variants of the defective half model are defect-free, the middle bits in the alternating model vanish.
-/

theorem cycle_power_dyadic_middle_bits_from_defective_halves (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
      (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t → x p j = false)
    (hnodefect : ∀ (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ),
      (shift = 0 ∨ shift = (2 : ℤ)^(t-1)) → cycle_power_dyadic_defective_half_model t y e shift → ∀ v, e v = false) :
    ∀ p : ℤ, x p 1 = false → x p (2^t - 1) = false ∧ x p (2^t) = false := by
  intro p hp
  obtain ⟨h0, h1⟩ := cycle_power_dyadic_alternating_defective_halves t ht x htight hexact hcover hcount
    halt hpart p hp
  have ht1 : 2 ^ t = 2 * 2 ^ (t-1) := by
    rw [← pow_succ']; congr 1; omega
  have ht2 : 1 ≤ 2 ^ (t-1) := Nat.one_le_two_pow
  have hr : p + 2 * (((2 ^ (t-1) : ℕ) : ℤ) - 1) + 2 - ((2^t : ℕ) : ℤ) = p := by
    rw [ht1]; push_cast; ring
  have e0 := hnodefect _ _ _ (Or.inl rfl) h0 (((2 ^ (t-1) : ℕ) : ℤ) - 1)
  have e1 := hnodefect _ _ _ (Or.inr rfl) h1 (((2 ^ (t-1) : ℕ) : ℤ) - 1)
  rw [hr] at e0 e1
  exact ⟨e0, e1⟩
