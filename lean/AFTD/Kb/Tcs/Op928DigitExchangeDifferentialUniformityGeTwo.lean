import AFTD.Prelude
import AFTD.Kb.Tcs.DigitExchangeDifferentialUniformity

/-!
# op_928_digit_exchange_differential_uniformity_ge_two

Topic: cryptography   Node: f2d60f1c7184

Provenance: formalization of a published result. Source: arXiv:2611.02572, Proposition 3.2

For every integer m ≥ 1 and every element c in GaloisField 2 m with absolute trace Algebra.trace (ZMod 2) (GaloisField 2 m) c = 1, the differential uniformity digit_exchange_differential_uniformity m c is at least 2.
-/

/-- Proposition 3.2 of arXiv:2611.02572: every permutation of (Z/4Z)^m has differential uniformity at least 2. -/
theorem op_928_digit_exchange_differential_uniformity_ge_two
    (m : ℕ) (hm : 1 ≤ m) (c : GaloisField 2 m)
    (hc : Algebra.trace (ZMod 2) (GaloisField 2 m) c = 1) :
    2 ≤ digit_exchange_differential_uniformity m c := by
  have _ := hc
  classical
  let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite (GaloisField 2 m)
  have : NeZero m := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero (GaloisField 2 m) 2
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (NeZero.ne m)
  have hf : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have hpow_card (y : GaloisField 2 m) : (y ^ 2) ^ (2 ^ (m - 1)) = y := by
    rw [← pow_mul, mul_comm 2, ← pow_succ, Nat.sub_add_cancel hm, ← hf, FiniteField.pow_card]
  have hpow : 2 ^ (m - 1) ≠ 0 := by positivity

  unfold digit_exchange_differential_uniformity
  dsimp only
  let α : GaloisField 2 m × GaloisField 2 m := (0, 1)
  let β : GaloisField 2 m × GaloisField 2 m := (c, 0)
  have hα_ne : α ≠ (0, 0) := by
    intro h
    have : (1 : GaloisField 2 m) = 0 := Prod.ext_iff.mp h |>.2
    exact one_ne_zero this

  refine le_trans ?_ (Finset.le_sup (b := α) ?_)
  · refine le_trans ?_ (Finset.le_sup (b := β) ?_)
    · let add (x y : GaloisField 2 m × GaloisField 2 m) : GaloisField 2 m × GaloisField 2 m :=
        (x.1 + y.1, x.2 + y.2 + (x.1 * y.1) ^ (2 ^ (m - 1)))
      let sub (y z : GaloisField 2 m × GaloisField 2 m) : GaloisField 2 m × GaloisField 2 m :=
        (y.1 + z.1, y.2 + z.1 + z.2 + (y.1 * z.1) ^ (2 ^ (m - 1)))
      let D (x : GaloisField 2 m) : GaloisField 2 m := x ^ 2 + x + c
      let G (x : GaloisField 2 m × GaloisField 2 m) : GaloisField 2 m × GaloisField 2 m :=
        let L := D x.1 * x.2
        (L, D L * x.1)
      change 2 ≤ (Finset.filter (fun x => sub (G (add x α)) (G x) = β) Finset.univ).card

      let x1 : GaloisField 2 m × GaloisField 2 m := (0, 0)
      let x2 : GaloisField 2 m × GaloisField 2 m := (1, (c + 1) ^ 2)

      have hx_ne : x1 ≠ x2 := by
        intro h
        have : (0 : GaloisField 2 m) = 1 := Prod.ext_iff.mp h |>.1
        exact zero_ne_one this

      have hsol1 : sub (G (add x1 α)) (G x1) = β := by
        ext <;> simp [α, β, x1, add, sub, D, G]

      have hsol2 : sub (G (add x2 α)) (G x2) = β := by
        ext
        · dsimp [α, β, x2, add, sub, D, G]
          simp only [mul_zero, zero_pow hpow, add_zero]
          linear_combination (c ^ 3 + 4 * c ^ 2 + 5 * c + 3) * h2
        · dsimp [α, β, x2, add, sub, D, G]
          simp only [mul_zero, zero_pow hpow, add_zero, mul_one]
          have hbase : (1 ^ 2 + 1 + c) * ((c + 1) ^ 2 + 1) * ((1 ^ 2 + 1 + c) * (c + 1) ^ 2) = (c ^ 2 * (c + 1)) ^ 2 := by
            linear_combination (4 + 16 * c + 27 * c ^ 2 + 25 * c ^ 3 + 13 * c ^ 4 + 3 * c ^ 5) * h2
          rw [hbase, hpow_card]
          linear_combination (14 + 43 * c + 61 * c ^ 2 + 52 * c ^ 3 + 27 * c ^ 4 + 8 * c ^ 5 + c ^ 6) * h2

      have h_sub : {x1, x2} ⊆ Finset.filter (fun x => sub (G (add x α)) (G x) = β) Finset.univ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsol1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsol2⟩

      have h2card : ({x1, x2} : Finset (GaloisField 2 m × GaloisField 2 m)).card = 2 := by
        simp [Finset.card_pair hx_ne]

      exact le_trans (le_of_eq h2card.symm) (Finset.card_le_card h_sub)
    · exact Finset.mem_univ β
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ α, hα_ne⟩
