import AFTD.Prelude
import AFTD.Kb.Tcs.DigitExchangeDifferentialUniformity

/-!
# op_928_digit_exchange_differential_uniformity_one

Topic: cryptography   Node: 1fb49617dc08

Provenance: formalization of a published result. Source: arXiv:2611.02572, Table 1

For m = 1 and any element c in GaloisField 2 1 with absolute trace Algebra.trace (ZMod 2) (GaloisField 2 1) c = 1, the differential uniformity digit_exchange_differential_uniformity 1 c is equal to 2.
-/

/-- Base case m = 1 (Table 1 of arXiv:2611.02572): differential uniformity of G_c is equal to 2. -/
theorem op_928_digit_exchange_differential_uniformity_one
    (c : GaloisField 2 1)
    (hc : Algebra.trace (ZMod 2) (GaloisField 2 1) c = 1) :
    digit_exchange_differential_uniformity 1 c = 2 := by
  classical
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by omega)]
    norm_num
  have h2 : (2 : GaloisField 2 1) = 0 := CharTwo.two_eq_zero
  have hsq : ∀ t : GaloisField 2 1, t ^ 2 = t := by
    intro t; have := FiniteField.pow_card t; rwa [hcard] at this
  have h01 : ∀ t : GaloisField 2 1, t = 0 ∨ t = 1 := by
    intro t
    have : t * (t - 1) = 0 := by linear_combination hsq t
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc1 : c = 1 := by
    rcases h01 c with h | h
    · rw [h, map_zero] at hc; exact absurd hc (by decide)
    · exact h
  subst hc1
  have hD : ∀ t : GaloisField 2 1, t ^ 2 + t + 1 = 1 := by
    intro t; rw [hsq]; linear_combination t * h2
  unfold digit_exchange_differential_uniformity
  simp only [Nat.sub_self, pow_zero, pow_one, hD, one_mul]
  have h10 : (1 : GaloisField 2 1) ≠ 0 := one_ne_zero
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨u, v⟩ huv
    apply Finset.sup_le
    rintro ⟨β1, β2⟩ _
    have hS : ∀ x ∈ Finset.univ.filter (fun x : GaloisField 2 1 × GaloisField 2 1 =>
        (x.2 + v + x.1 * u + x.2, x.1 + u + x.2 + x.1 + (x.2 + v + x.1 * u) * x.2) = (β1, β2)),
        x.2 + v + x.1 * u + x.2 = β1 ∧ x.1 + u + x.2 + x.1 + (x.2 + v + x.1 * u) * x.2 = β2 := by
      intro x hx
      rw [Finset.mem_filter, Prod.mk.injEq] at hx
      exact hx.2
    have hle : ∀ (f : GaloisField 2 1 × GaloisField 2 1 → GaloisField 2 1),
        Set.InjOn f ↑(Finset.univ.filter (fun x : GaloisField 2 1 × GaloisField 2 1 =>
        (x.2 + v + x.1 * u + x.2, x.1 + u + x.2 + x.1 + (x.2 + v + x.1 * u) * x.2) = (β1, β2))) →
        (Finset.univ.filter (fun x : GaloisField 2 1 × GaloisField 2 1 =>
        (x.2 + v + x.1 * u + x.2, x.1 + u + x.2 + x.1 + (x.2 + v + x.1 * u) * x.2) = (β1, β2))).card
          ≤ 2 := by
      intro f hf
      calc _ ≤ (Finset.univ : Finset (GaloisField 2 1)).card :=
            Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hf
        _ = 2 := by rw [Finset.card_univ, hcard]
    rcases h01 u with rfl | rfl
    · have hv : v = 1 := by
        rcases h01 v with rfl | h
        · exact absurd rfl (Finset.mem_filter.mp huv).2
        · exact h
      subst hv
      apply hle (fun x => x.1)
      intro x hx y hy hxy
      have ex := (hS x hx).2
      have ey := (hS y hy).2
      have e2x : x.2 = β2 := by linear_combination ex + (-(x.1 + x.2)) * h2 + (-1) * hsq x.2
      have e2y : y.2 = β2 := by linear_combination ey + (-(y.1 + y.2)) * h2 + (-1) * hsq y.2
      exact Prod.ext hxy (e2x.trans e2y.symm)
    · apply hle (fun x => x.2)
      intro x hx y hy hxy
      have ex := (hS x hx).1
      have ey := (hS y hy).1
      have e1x : x.1 = β1 - v := by linear_combination ex + (-x.2) * h2
      have e1y : y.1 = β1 - v := by linear_combination ey + (-y.2) * h2
      exact Prod.ext (e1x.trans e1y.symm) hxy
  · have hα : ((0 : GaloisField 2 1), (1 : GaloisField 2 1)) ∈
        Finset.univ.filter (fun α : GaloisField 2 1 × GaloisField 2 1 => α ≠ (0, 0)) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h; rw [Prod.mk.injEq] at h; exact h10 h.2
    refine le_trans ?_ (Finset.le_sup hα)
    refine le_trans ?_ (Finset.le_sup (Finset.mem_univ ((1 : GaloisField 2 1), (0 : GaloisField 2 1))))
    have hsub : ({(0, 0), (1, 0)} : Finset (GaloisField 2 1 × GaloisField 2 1)) ⊆
        Finset.univ.filter (fun x : GaloisField 2 1 × GaloisField 2 1 =>
        (x.2 + (0, 1).2 + x.1 * (0, 1).1 + x.2,
          x.1 + (0, 1).1 + x.2 + x.1 + (x.2 + (0, 1).2 + x.1 * (0, 1).1) * x.2) =
          ((1 : GaloisField 2 1), (0 : GaloisField 2 1))) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx with rfl | rfl
      · simp
      · simp only [Prod.mk.injEq]
        constructor
        · ring
        · linear_combination h2
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_pair]
    intro h; rw [Prod.mk.injEq] at h; exact h10 h.1.symm
