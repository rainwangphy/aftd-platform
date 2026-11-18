import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPrime5AnchoredLine

/-!
# good_slopes_prime5_three_unit_directions_line

Topic: elementary_number_theory   Node: 0a6268e3da40

Provenance: helper lemma. Five-point slice step for OP-1027.

Five points in the plane over the field of five elements have injective forms y+ax for every nonzero a other than b, where b is nonzero. If y+bx fails to be injective, it is constant on the five points.
-/

theorem good_slopes_prime5_three_unit_directions_line_two_ne_zero : (2 : ZMod 5) ≠ 0 := by decide
theorem good_slopes_prime5_three_unit_directions_line_three_ne_zero : (3 : ZMod 5) ≠ 0 := by decide
theorem good_slopes_prime5_three_unit_directions_line_four_ne_zero : (4 : ZMod 5) ≠ 0 := by decide
theorem good_slopes_prime5_three_unit_directions_line_two_ne_one : (2 : ZMod 5) ≠ 1 := by decide
theorem good_slopes_prime5_three_unit_directions_line_three_ne_one : (3 : ZMod 5) ≠ 1 := by decide
theorem good_slopes_prime5_three_unit_directions_line_four_ne_one : (4 : ZMod 5) ≠ 1 := by decide

theorem good_slopes_prime5_three_unit_directions_line
    (S : Finset (ZMod 5 × ZMod 5)) (b : ZMod 5)
    (hcard : S.card = 5) (hb : IsUnit b)
    (hgood : ∀ a : ZMod 5, IsUnit a → a ≠ b →
      Set.InjOn (fun p : ZMod 5 × ZMod 5 => p.2 + a*p.1) S)
    (hbad : ¬ Set.InjOn (fun p : ZMod 5 × ZMod 5 => p.2 + b*p.1) S) :
    ∃ t : ZMod 5, ∀ p ∈ S, p.2 + b*p.1 = t := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hb0 : b ≠ 0 := hb.ne_zero
  dsimp [Set.InjOn] at hbad
  push Not at hbad
  rcases hbad with ⟨p0, hp0, p1, hp1, heq, hne⟩
  rw [Finset.mem_coe] at hp0 hp1
  set u := p1.1 - p0.1 with hu_def
  have hu : u ≠ 0 := by
    intro h
    have hx : p1.1 = p0.1 := sub_eq_zero.mp h
    have hy : p1.2 = p0.2 := by
      have := heq.symm
      rw [hx] at this
      exact add_right_cancel this
    apply hne
    ext
    · exact hx.symm
    · exact hy.symm
  have hbu : b * u ≠ 0 := mul_ne_zero hb0 hu
  set f : ZMod 5 × ZMod 5 → ZMod 5 × ZMod 5 :=
    fun p => (u⁻¹ * (p.1 - p0.1), (b * u)⁻¹ * (p.2 - p0.2)) with hf_def
  have hf_inj : Function.Injective f := by
    intro p q h
    dsimp [f] at h
    injection h with h1 h2
    have hu' : u⁻¹ ≠ 0 := inv_ne_zero hu
    have hbu' : (b * u)⁻¹ ≠ 0 := inv_ne_zero hbu
    have h1' := mul_left_cancel₀ hu' h1
    have h2' := mul_left_cancel₀ hbu' h2
    ext
    · exact sub_left_inj.mp h1'
    · exact sub_left_inj.mp h2'
  have hfp0 : f p0 = (0, 0) := by
    ext <;> dsimp [f] <;> simp
  have hfp1 : f p1 = (1, 4) := by
    ext
    · dsimp [f]
      rw [← hu_def, inv_mul_cancel₀ hu]
    · dsimp [f]
      have h : p1.2 - p0.2 = - (b * u) := by
        calc p1.2 - p0.2 = - (b * (p1.1 - p0.1)) := by
              linear_combination -heq
             _ = - (b * u) := by rw [hu_def]
      rw [h, mul_neg, inv_mul_cancel₀ hbu]
      rfl
  set S' := S.image f with hS'_def
  have hcard' : S'.card = 5 := by
    rw [hS'_def, Finset.card_image_of_injective S hf_inj, hcard]
  have h0 : (0, 0) ∈ S' := by
    rw [← hfp0]
    exact Finset.mem_image_of_mem f hp0
  have h1 : (1, 4) ∈ S' := by
    rw [← hfp1]
    exact Finset.mem_image_of_mem f hp1
  have h_form_inj (c : ZMod 5) (hc : c = 2 ∨ c = 3 ∨ c = 4) :
      Set.InjOn (fun (p : ZMod 5 × ZMod 5) => p.2 + c * p.1) S' := by
    have hc0 : c ≠ 0 := by
      rcases hc with rfl | rfl | rfl
      · exact good_slopes_prime5_three_unit_directions_line_two_ne_zero
      · exact good_slopes_prime5_three_unit_directions_line_three_ne_zero
      · exact good_slopes_prime5_three_unit_directions_line_four_ne_zero
    have hc1 : c ≠ 1 := by
      rcases hc with rfl | rfl | rfl
      · exact good_slopes_prime5_three_unit_directions_line_two_ne_one
      · exact good_slopes_prime5_three_unit_directions_line_three_ne_one
      · exact good_slopes_prime5_three_unit_directions_line_four_ne_one
    have ha_unit : IsUnit (b * c) := by
      rw [isUnit_iff_ne_zero]
      exact mul_ne_zero hb0 hc0
    have ha_ne : b * c ≠ b := by
      intro h
      have hbc : b * c = b * 1 := by rw [h, mul_one]
      have := mul_left_cancel₀ hb0 hbc
      exact hc1 this
    have h_inj := hgood (b * c) ha_unit ha_ne
    intro P hP Q hQ h_eval
    rw [Finset.mem_coe, Finset.mem_image] at hP hQ
    rcases hP with ⟨p, hp, rfl⟩
    rcases hQ with ⟨q, hq, rfl⟩
    dsimp at h_eval
    have h_eq (r : ZMod 5 × ZMod 5) :
      (b * u) * ((f r).2 + c * (f r).1) = (r.2 + (b * c) * r.1) - (p0.2 + (b * c) * p0.1) := by
      dsimp [f]
      rw [mul_add, ← mul_assoc (b * u), mul_inv_cancel₀ hbu, one_mul]
      have : (b * u) * (c * (u⁻¹ * (r.1 - p0.1))) = (b * c) * (r.1 - p0.1) := by
        calc (b * u) * (c * (u⁻¹ * (r.1 - p0.1)))
          _ = (b * c) * (u * u⁻¹) * (r.1 - p0.1) := by ring
          _ = (b * c) * 1 * (r.1 - p0.1) := by rw [mul_inv_cancel₀ hu]
          _ = (b * c) * (r.1 - p0.1) := by ring
      rw [this]
      ring
    have h1 : (b * u) * ((f p).2 + c * (f p).1) = (b * u) * ((f q).2 + c * (f q).1) := by rw [h_eval]
    rw [h_eq p, h_eq q] at h1
    have h2 : p.2 + (b * c) * p.1 = q.2 + (b * c) * q.1 := sub_left_inj.mp h1
    have hpq : p = q := h_inj hp hq h2
    rw [hpq]
  have h2 : Set.InjOn (fun (p : ZMod 5 × ZMod 5) => p.2 + 2 * p.1) S' :=
    h_form_inj 2 (Or.inl rfl)
  have h3 : Set.InjOn (fun (p : ZMod 5 × ZMod 5) => p.2 + 3 * p.1) S' :=
    h_form_inj 3 (Or.inr (Or.inl rfl))
  have h4 : Set.InjOn (fun (p : ZMod 5 × ZMod 5) => p.2 + 4 * p.1) S' :=
    h_form_inj 4 (Or.inr (Or.inr rfl))
  have h_line := good_slopes_prime5_anchored_line S' hcard' h0 h1 h2 h3 h4
  use p0.2 + b * p0.1
  intro p hp
  have hfp_mem : f p ∈ S' := Finset.mem_image_of_mem f hp
  have h_zero := h_line (f p) hfp_mem
  have h_eq :
    (b * u) * ((f p).2 + 1 * (f p).1) = (p.2 + (b * 1) * p.1) - (p0.2 + (b * 1) * p0.1) := by
    dsimp [f]
    rw [mul_add, ← mul_assoc (b * u), mul_inv_cancel₀ hbu, one_mul]
    have : (b * u) * (1 * (u⁻¹ * (p.1 - p0.1))) = (b * 1) * (p.1 - p0.1) := by
      calc (b * u) * (1 * (u⁻¹ * (p.1 - p0.1)))
        _ = (b * 1) * (u * u⁻¹) * (p.1 - p0.1) := by ring
        _ = (b * 1) * 1 * (p.1 - p0.1) := by rw [mul_inv_cancel₀ hu]
        _ = (b * 1) * (p.1 - p0.1) := by ring
    rw [this]
    ring
  rw [mul_one] at h_eq
  have h_f_zero : ((f p).2 + 1 * (f p).1) = 0 := by
    calc ((f p).2 + 1 * (f p).1)
      _ = (f p).2 + (f p).1 := by rw [one_mul]
      _ = 0 := h_zero
  rw [h_f_zero, mul_zero] at h_eq
  exact sub_eq_zero.mp h_eq.symm
