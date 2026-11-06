import AFTD.Prelude
import AFTD.Kb.Tcs.DigitExchangeDifferentialUniformity
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# op_928_digit_exchange_differential_uniformity_le_thirty_six

Topic: cryptography   Node: d3232cbe9244

Provenance: formalization of a published result. Source: arXiv:2611.02572, Theorem 1.1

For every integer m ≥ 1 and every element c in GaloisField 2 m with absolute trace Algebra.trace (ZMod 2) (GaloisField 2 m) c = 1, the differential uniformity digit_exchange_differential_uniformity m c is at most 36.
-/

open Polynomial in
theorem op928_de_poly36_natDegree {F : Type*} [Field F] (u v σ c β1 β2 κ : F)
    (hu : u ≠ 0) (hσ : σ ≠ 0) (hκ : κ ≠ 0) (W DaP DauP bP LP L'P QP : F[X])
    (hW : W = C v + C σ * X) (hDa : DaP = X ^ 4 + X ^ 2 + C c)
    (hDau : DauP = (X ^ 2 + C u) ^ 2 + (X ^ 2 + C u) + C c)
    (hb : bP = C κ⁻¹ * (C β1 + DauP * W)) (hL : LP = DaP * bP) (hL' : L'P = DauP * (bP + W))
    (hQ : QP = C u * (L'P ^ 2 + L'P + C c) + C (β1 ^ 2 + β1) * X ^ 2 + LP + C β2) :
    (QP ^ 2 - L'P * LP).natDegree = 36 := by
  subst hQ hL hL' hb hW hDa hDau
  compute_degree!

theorem op928_de_key {F : Type*} [Field F] (h2 : (2:F) = 0) (N : ℕ) (hN : ∀ t : F, (t ^ N) ^ 2 = t)
    (c u β1 β2 a L L' : F)
    (E1 : L' + L = β1)
    (E2 : (L' ^ 2 + L' + c) * (a + u) + L + (L ^ 2 + L + c) * a + (L' * L) ^ N = β2) :
    (u * (L' ^ 2 + L' + c) + (β1 ^ 2 + β1) * a + L + β2) ^ 2 = L' * L := by
  have hQ : u * (L' ^ 2 + L' + c) + (β1 ^ 2 + β1) * a + L + β2 = (L' * L) ^ N := by
    linear_combination (-(β1 + L' + L + 1) * a) * E1 - E2 +
      (u * (L' ^ 2 + L' + c) + a * (L' ^ 2 + L' * L + L ^ 2 + L' + L + c) + L) * h2
  rw [hQ, hN]

open Polynomial in
theorem op928_de_fiber_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] (h2 : (2:F) = 0) (N : ℕ)
    (hN : ∀ t : F, (t ^ N) ^ 2 = t) (c : F) (hD : ∀ t : F, t ^ 2 + t + c ≠ 0)
    (u v β1 β2 : F) (huv : ¬ (u = 0 ∧ v = 0)) (S : Finset (F × F))
    (hS : ∀ x ∈ S,
      ((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N) + (x.1 ^ 2 + x.1 + c) * x.2 = β1 ∧
      ((((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N)) ^ 2 +
        ((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N) + c) * (x.1 + u) +
        (x.1 ^ 2 + x.1 + c) * x.2 +
        (((x.1 ^ 2 + x.1 + c) * x.2) ^ 2 + (x.1 ^ 2 + x.1 + c) * x.2 + c) * x.1 +
        (((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N) * ((x.1 ^ 2 + x.1 + c) * x.2)) ^ N
        = β2) :
    S.card ≤ 36 := by
  have hsq : ∀ s t : F, s ^ 2 = t ^ 2 → s = t := by
    intro s t h
    have e : ∀ s : F, (s ^ 2) ^ N = s := fun s => by rw [← pow_mul, mul_comm, pow_mul, hN]
    rw [← e s, h, e t]
  have hN0 : N ≠ 0 := by
    intro h; have := hN 0; rw [h] at this; simp at this
  have h0N : (0:F) ^ N = 0 := zero_pow hN0
  -- consequences for one solution
  have key : ∀ x ∈ S,
      (((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N)) + (x.1 ^ 2 + x.1 + c) * x.2 = β1 ∧
      (u * ((((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N)) ^ 2 +
        ((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N) + c) + (β1 ^ 2 + β1) * x.1 +
        (x.1 ^ 2 + x.1 + c) * x.2 + β2) ^ 2 =
        (((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N)) * ((x.1 ^ 2 + x.1 + c) * x.2) := by
    intro x hx
    obtain ⟨E1, E2⟩ := hS x hx
    exact ⟨E1, op928_de_key h2 N hN c u β1 β2 x.1 _ _ E1 E2⟩
  by_cases hu0 : u = 0
  · -- u = 0, v ≠ 0
    have hv : v ≠ 0 := fun hv => huv ⟨hu0, hv⟩
    subst hu0
    obtain ⟨P, hP⟩ : ∃ P : F[X], P = C v * (X ^ 2 + X + C c) - C β1 := ⟨_, rfl⟩
    have hPd : P.natDegree = 2 := by subst hP; compute_degree!
    have hP0 : P ≠ 0 := by intro h; rw [h] at hPd; simp at hPd
    have hdat : ∀ x ∈ S, (x.1 ^ 2 + x.1 + c) * v = β1 ∧
        β1 * ((x.1 ^ 2 + x.1 + c) * x.2) = ((β1 ^ 2 + β1) * x.1 + β2) ^ 2 := by
      intro x hx
      obtain ⟨E1, E2⟩ := key x hx
      simp only [add_zero, mul_zero, h0N, zero_mul, zero_add] at E1 E2
      have hE1 : (x.1 ^ 2 + x.1 + c) * v = β1 := by
        linear_combination E1 + (-(x.1 ^ 2 + x.1 + c) * x.2) * h2
      refine ⟨hE1, ?_⟩
      have hL' : (x.1 ^ 2 + x.1 + c) * (x.2 + v) = β1 - (x.1 ^ 2 + x.1 + c) * x.2 := by
        linear_combination E1
      rw [hL'] at E2
      linear_combination (-1) * E2 + (((x.1 ^ 2 + x.1 + c) * x.2) ^ 2 +
        ((x.1 ^ 2 + x.1 + c) * x.2) * ((β1 ^ 2 + β1) * x.1 + β2)) * h2
    calc S.card ≤ P.roots.toFinset.card := by
          apply Finset.card_le_card_of_injOn (fun x => x.1)
          · intro x hx
            rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
            simp only [eval_sub, eval_mul, eval_C, eval_add, eval_pow, eval_X]
            rw [mul_comm, (hdat x hx).1, sub_self]
          · intro x hx y hy hxy
            simp only at hxy
            have hb1 : β1 ≠ 0 := by
              rw [← (hdat x hx).1]; exact mul_ne_zero (hD _) hv
            have h1 := (hdat x hx).2
            have h2' := (hdat y hy).2
            rw [hxy] at h1
            rw [← h2'] at h1
            have := mul_left_cancel₀ hb1 h1
            have := mul_left_cancel₀ (hD _) this
            exact Prod.ext hxy this
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ ≤ 36 := by omega
  by_cases hu1 : u = 1
  · subst hu1
    obtain ⟨P, hP⟩ : ∃ P : F[X], P = (X ^ 4 + X ^ 2 + C c) * (C v + X) - C β1 := ⟨_, rfl⟩
    have hPd : P.natDegree = 5 := by subst hP; compute_degree!
    have hP0 : P ≠ 0 := by intro h; rw [h] at hPd; simp at hPd
    let R : F → F[X] := fun A => (X ^ 2 + C (β1 ^ 2 + β1 + c + (β1 ^ 2 + β1) * A ^ 2 + β2)) ^ 2
      - (C β1 - X) * X
    have hRd : ∀ A, (R A).natDegree = 4 := by intro A; simp only [R]; compute_degree!
    have hR0 : ∀ A, R A ≠ 0 := by intro A h; have := hRd A; rw [h] at this; simp at this
    have hdat : ∀ x ∈ S, eval (x.1 ^ N) P = 0 ∧
        eval ((x.1 ^ 2 + x.1 + c) * x.2) (R (x.1 ^ N)) = 0 := by
      intro x hx
      obtain ⟨E1, E2⟩ := key x hx
      simp only [mul_one, one_mul] at E1 E2
      have ha := hN x.1
      constructor
      · rw [hP]
        simp only [eval_sub, eval_mul, eval_C, eval_add, eval_pow, eval_X]
        rw [show (x.1 ^ N) ^ 4 = ((x.1 ^ N) ^ 2) ^ 2 by ring, ha]
        linear_combination E1 + (-((x.1 ^ 2 + x.1 + c) * x.2) -
          (x.1 + 1) * (x.2 + v + x.1 ^ N)) * h2
      · have hL' : ((x.1 + 1) ^ 2 + (x.1 + 1) + c) * (x.2 + v + x.1 ^ N) =
            β1 - (x.1 ^ 2 + x.1 + c) * x.2 := by linear_combination E1
        rw [hL'] at E2
        simp only [R, eval_sub, eval_mul, eval_C, eval_add, eval_pow, eval_X]
        rw [ha]
        linear_combination E2 + (β1 * ((x.1 ^ 2 + x.1 + c) * x.2) *
          (((x.1 ^ 2 + x.1 + c) * x.2) ^ 2 + (β1 ^ 2 + β1 + c + (β1 ^ 2 + β1) * x.1 + β2) +
            (((β1 - (x.1 ^ 2 + x.1 + c) * x.2) ^ 2 + (β1 - (x.1 ^ 2 + x.1 + c) * x.2) + c) +
              (β1 ^ 2 + β1) * x.1 + (x.1 ^ 2 + x.1 + c) * x.2 + β2))) * h2
    calc S.card ≤ (P.roots.toFinset.biUnion
          (fun A => (R A).roots.toFinset.image (fun L => (A, L)))).card := by
          apply Finset.card_le_card_of_injOn (fun x => (x.1 ^ N, (x.1 ^ 2 + x.1 + c) * x.2))
          · intro x hx
            rw [Finset.mem_coe, Finset.mem_biUnion]
            refine ⟨x.1 ^ N, ?_, ?_⟩
            · rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]; exact (hdat x hx).1
            · rw [Finset.mem_image]
              refine ⟨(x.1 ^ 2 + x.1 + c) * x.2, ?_, rfl⟩
              rw [Multiset.mem_toFinset, mem_roots (hR0 _), IsRoot.def]; exact (hdat x hx).2
          · intro x _ y _ hxy
            simp only [Prod.mk.injEq] at hxy
            have h1 : x.1 = y.1 := by rw [← hN x.1, ← hN y.1, hxy.1]
            have h3 := hxy.2
            rw [h1] at h3
            exact Prod.ext h1 (mul_left_cancel₀ (hD _) h3)
      _ ≤ ∑ A ∈ P.roots.toFinset, ((R A).roots.toFinset.image (fun L => (A, L))).card :=
          Finset.card_biUnion_le
      _ ≤ P.roots.toFinset.card • 4 := by
          apply Finset.sum_le_card_nsmul
          intro A _
          calc _ ≤ (R A).roots.toFinset.card := Finset.card_image_le
            _ ≤ (R A).roots.card := Multiset.toFinset_card_le _
            _ ≤ (R A).natDegree := card_roots' _
            _ = 4 := hRd A
      _ ≤ 5 • 4 := by
          apply Nat.mul_le_mul_right
          calc _ ≤ P.roots.card := Multiset.toFinset_card_le _
            _ ≤ P.natDegree := card_roots' _
            _ = 5 := hPd
      _ ≤ 36 := by norm_num
  -- generic case
  set σ := u ^ N with hσdef
  have hσ : σ ≠ 0 := by intro h; apply hu0; rw [← hN u, ← hσdef, h]; ring
  set κ := u ^ 2 + u with hκdef
  have hκ : κ ≠ 0 := by
    rw [hκdef, show u ^ 2 + u = u * (u + 1) by ring]
    refine mul_ne_zero hu0 ?_
    intro h; apply hu1; linear_combination h - h2
  obtain ⟨W, hW⟩ : ∃ W : F[X], W = C v + C σ * X := ⟨_, rfl⟩
  obtain ⟨DaP, hDa⟩ : ∃ DaP : F[X], DaP = X ^ 4 + X ^ 2 + C c := ⟨_, rfl⟩
  obtain ⟨DauP, hDau⟩ : ∃ DauP : F[X], DauP = (X ^ 2 + C u) ^ 2 + (X ^ 2 + C u) + C c := ⟨_, rfl⟩
  obtain ⟨bP, hb⟩ : ∃ bP : F[X], bP = C κ⁻¹ * (C β1 + DauP * W) := ⟨_, rfl⟩
  obtain ⟨LP, hL⟩ : ∃ LP : F[X], LP = DaP * bP := ⟨_, rfl⟩
  obtain ⟨L'P, hL'⟩ : ∃ L'P : F[X], L'P = DauP * (bP + W) := ⟨_, rfl⟩
  obtain ⟨QP, hQ⟩ : ∃ QP : F[X],
    QP = C u * (L'P ^ 2 + L'P + C c) + C (β1 ^ 2 + β1) * X ^ 2 + LP + C β2 := ⟨_, rfl⟩
  have hPd := op928_de_poly36_natDegree u v σ c β1 β2 κ hu0 hσ hκ W DaP DauP bP LP L'P QP
    hW hDa hDau hb hL hL' hQ
  have hP0 : QP ^ 2 - L'P * LP ≠ 0 := by intro h; rw [h] at hPd; simp at hPd
  have hbx : ∀ x ∈ S, κ * x.2 = β1 + ((x.1 + u) ^ 2 + (x.1 + u) + c) * (v + x.1 ^ N * σ) := by
    intro x hx
    obtain ⟨E1, _⟩ := key x hx
    rw [mul_pow] at E1
    linear_combination E1 + (-((x.1 + u) ^ 2 + (x.1 + u) + c) * (v + x.1 ^ N * σ) -
      (x.1 ^ 2 + x.1 + c) * x.2 - x.1 * u * x.2) * h2
  have hroot : ∀ x ∈ S, eval (x.1 ^ N) (QP ^ 2 - L'P * LP) = 0 := by
    intro x hx
    obtain ⟨_, E2⟩ := key x hx
    have ha := hN x.1
    set A := x.1 ^ N with hA
    have eDa : eval A DaP = x.1 ^ 2 + x.1 + c := by
      rw [hDa]; simp only [eval_add, eval_pow, eval_X, eval_C]
      rw [show A ^ 4 = (A ^ 2) ^ 2 by ring, ha]
    have eDau : eval A DauP = (x.1 + u) ^ 2 + (x.1 + u) + c := by
      rw [hDau]; simp only [eval_add, eval_pow, eval_X, eval_C]; rw [ha]
    have eW : eval A W = v + A * σ := by
      rw [hW]; simp only [eval_add, eval_mul, eval_X, eval_C]; ring
    have eb : eval A bP = x.2 := by
      rw [hb]; simp only [eval_add, eval_mul, eval_C]
      rw [eDau, eW, ← hbx x hx]
      field_simp
    have eL : eval A LP = (x.1 ^ 2 + x.1 + c) * x.2 := by
      rw [hL, eval_mul, eDa, eb]
    have eL' : eval A L'P = ((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N) := by
      rw [hL', eval_mul, eval_add, eDau, eb, eW, mul_pow, ← hσdef]; ring
    have eQ : eval A QP = u * ((((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N)) ^ 2 +
        ((x.1 + u) ^ 2 + (x.1 + u) + c) * (x.2 + v + (x.1 * u) ^ N) + c) + (β1 ^ 2 + β1) * x.1 +
        (x.1 ^ 2 + x.1 + c) * x.2 + β2 := by
      rw [hQ]; simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
      rw [eL', eL, ha]
    rw [eval_sub, eval_pow, eval_mul, eQ, eL', eL, E2, sub_self]
  calc S.card ≤ (QP ^ 2 - L'P * LP).roots.toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun x => x.1 ^ N)
        · intro x hx
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]
          exact hroot x hx
        · intro x hx y hy hxy
          simp only at hxy
          have h1 : x.1 = y.1 := by rw [← hN x.1, ← hN y.1, hxy]
          have h3 := hbx x hx
          rw [h1, ← hbx y hy] at h3
          exact Prod.ext h1 (mul_left_cancel₀ hκ h3)
    _ ≤ (QP ^ 2 - L'P * LP).roots.card := Multiset.toFinset_card_le _
    _ ≤ (QP ^ 2 - L'P * LP).natDegree := card_roots' _
    _ = 36 := hPd

theorem op928_de_trace_sq_add_self (m : ℕ) (x : GaloisField 2 m) :
    Algebra.trace (ZMod 2) (GaloisField 2 m) (x ^ 2 + x) = 0 := by
  have : Fintype (GaloisField 2 m) := Fintype.ofFinite (GaloisField 2 m)
  have : ExpChar (GaloisField 2 m) 2 := ExpChar.prime Nat.prime_two
  have h1 : (FiniteField.frobeniusAlgEquiv (ZMod 2) (GaloisField 2 m) 2) x = x ^ 2 := by
    change FiniteField.frobeniusAlgHom (ZMod 2) (GaloisField 2 m) x = x ^ 2
    rw [FiniteField.coe_frobeniusAlgHom]
    change x ^ Fintype.card (ZMod 2) = x ^ 2
    rw [ZMod.card]
  have h2 : Algebra.trace (ZMod 2) (GaloisField 2 m) (x ^ 2) =
      Algebra.trace (ZMod 2) (GaloisField 2 m) x := by
    rw [← h1, Algebra.trace_eq_of_algEquiv]
  rw [map_add, h2]
  exact CharTwo.add_self_eq_zero _

/-- Theorem 1.1 of arXiv:2611.02572: the differential uniformity of G_c is at most 36 for all m ≥ 1 and all trace-one c. -/
theorem op_928_digit_exchange_differential_uniformity_le_thirty_six
    (m : ℕ) (hm : 1 ≤ m) (c : GaloisField 2 m)
    (hc : Algebra.trace (ZMod 2) (GaloisField 2 m) c = 1) :
    digit_exchange_differential_uniformity m c ≤ 36 := by
  classical
  have hD : ∀ x : GaloisField 2 m, x ^ 2 + x + c ≠ 0 := by
    intro x h
    have htr : Algebra.trace (ZMod 2) (GaloisField 2 m) (x ^ 2 + x + c) = 0 := by
      rw [h, map_zero]
    rw [map_add, op928_de_trace_sq_add_self, zero_add, hc] at htr
    revert htr
    decide
  have h2 : (2 : GaloisField 2 m) = 0 := CharTwo.two_eq_zero
  unfold digit_exchange_differential_uniformity
  simp only
  apply Finset.sup_le
  rintro ⟨u, v⟩ huv
  apply Finset.sup_le
  rintro ⟨β1, β2⟩ _
  have hN : ∀ t : GaloisField 2 m, (t ^ (2 ^ (m - 1))) ^ 2 = t := by
    intro t
    let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite _
    rw [← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega]
    have hcard : Fintype.card (GaloisField 2 m) = 2 ^ m := by
      rw [← Nat.card_eq_fintype_card, ← GaloisField.card 2 m (by omega), Nat.card_eq_fintype_card]
    rw [← hcard]
    exact FiniteField.pow_card t
  have huv' : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨rfl, rfl⟩
    simp at huv
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  apply op928_de_fiber_le h2 (2 ^ (m - 1)) hN c hD u v β1 β2 huv'
  intro x hx
  rw [Finset.mem_filter] at hx
  simpa only [Prod.mk.injEq] using hx.2
