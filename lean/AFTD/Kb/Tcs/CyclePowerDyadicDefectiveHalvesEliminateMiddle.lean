import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel

/-!
# cycle_power_dyadic_defective_halves_eliminate_middle

Topic: combinatorics   Node: 80c65ab449bf

Provenance: helper lemma. Indexing assembly for the RT-1 middle-bit reduction.

The two phase-specific defect-free half models eliminate both middle bits at a fixed root.
-/

theorem cycle_power_dyadic_defective_halves_eliminate_middle
    (t : ℕ) (ht : 1 ≤ t) (x : ℤ → ℕ → Bool) (s : ℤ)
    (hno : ∀ (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ),
      (shift = 0 ∨ shift = (2 : ℤ)^(t-1)) →
      cycle_power_dyadic_defective_half_model t y e shift → ∀ v, e v = false)
    (h0 : cycle_power_dyadic_defective_half_model t (fun q a => x (s + 2*q + 1) (2*a))
      (fun v => x (s + 2*v + 2 - ((2^t : ℕ) : ℤ)) (2^t - 1)) 0)
    (h1 : cycle_power_dyadic_defective_half_model t (fun q a => x (s + 2*q + 1) (2*a+1))
      (fun v => x (s + 2*v + 2 - ((2^t : ℕ) : ℤ)) (2^t)) ((2 : ℤ)^(t-1))) :
    x s (2^t - 1) = false ∧ x s (2^t) = false := by
  have hnat : (2:ℕ)^t = 2 * 2^(t-1) := by
    have hh : t = (t-1)+1 := by omega
    conv_lhs => rw [hh, pow_succ]
    omega
  have hint : ((2^t : ℕ) : ℤ) = 2 * ((2^(t-1) : ℕ) : ℤ) := by exact_mod_cast hnat
  let v : ℤ := ((2^(t-1) : ℕ) : ℤ) - 1
  have hv : s + 2*v + 2 - ((2^t : ℕ) : ℤ) = s := by dsimp [v]; push_cast at hint ⊢; omega
  have a := hno (fun q a => x (s+2*q+1) (2*a))
    (fun v => x (s+2*v+2-((2^t:ℕ):ℤ)) (2^t-1)) 0 (Or.inl rfl) h0 v
  have b := hno (fun q a => x (s+2*q+1) (2*a+1))
    (fun v => x (s+2*v+2-((2^t:ℕ):ℤ)) (2^t)) ((2:ℤ)^(t-1)) (Or.inr rfl) h1 v
  rw [hv] at a b
  exact ⟨a,b⟩
