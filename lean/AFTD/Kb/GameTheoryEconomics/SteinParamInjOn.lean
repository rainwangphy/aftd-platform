import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SteinParamSet
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.MuStar
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.G

/-!
# stein_param_inj_on

Topic: combinatorial_games   Node: 74eae7b0ba9c

Provenance: helper lemma. arXiv:2611.05898, Theorem 2.2

The map sending (d, u, v) to d^2 * (u^4 + 4 * v^4) is injective on stein_param_set.
-/

private lemma sp_n_eq (d u v : ℕ) :
    d^2 * (u^4 + 4*v^4)
      = (2*d*u*v)^2 + (d * (((u:ℤ)^2 - 2*(v:ℤ)^2).natAbs))^2 := by
  apply Int.natCast_inj.mp
  push_cast
  nlinarith [sq_abs ((u:ℤ)^2 - 2*(v:ℤ)^2)]

private lemma sp_A_sq (d u v : ℕ) :
    (d*(u^2+2*v^2))^2 = d^2 * (u^4 + 4*v^4) + (2*d*u*v)^2 := by
  ring

private lemma sp_sq_inj {a b : ℕ} (h : a^2 = b^2) : a = b := by
  have h2 := congrArg Nat.sqrt h
  rwa [Nat.sqrt_eq', Nat.sqrt_eq'] at h2

private lemma sp_sqrt (d u v : ℕ) (hd : 0 < d)
    (hineq : (d:ℤ) * ((u:ℤ)^2 - 2*(v:ℤ)^2)^2 ≤ 4*(u:ℤ)*(v:ℤ)) :
    Nat.sqrt (d^2 * (u^4 + 4*v^4)) = 2*d*u*v := by
  set p : ℕ := d * (((u:ℤ)^2 - 2*(v:ℤ)^2).natAbs)
  set m : ℕ := 2*d*u*v
  have hn : d^2 * (u^4 + 4*v^4) = m^2 + p^2 := by
    simpa [m, p] using sp_n_eq d u v
  rw [eq_comm, Nat.eq_sqrt]
  constructor
  · rw [hn]; simp only [pow_two]; exact Nat.le_add_right _ _
  · have hp2 : p^2 ≤ 2*m := by
      have hcast : ((p:ℤ))^2 = (d:ℤ)^2 * ((u:ℤ)^2 - 2*(v:ℤ)^2)^2 := by
        simp only [p]
        push_cast
        nlinarith [sq_abs ((u:ℤ)^2 - 2*(v:ℤ)^2)]
      have hdz : (0:ℤ) < d := by exact_mod_cast hd
      have hmul : (d:ℤ) * ((d:ℤ) * ((u:ℤ)^2 - 2*(v:ℤ)^2)^2) ≤ (d:ℤ) * (4*(u:ℤ)*(v:ℤ)) :=
        mul_le_mul_of_nonneg_left hineq (le_of_lt hdz)
      have : ((p^2:ℕ):ℤ) ≤ ((2*m:ℕ):ℤ) := by
        push_cast
        nlinarith [hcast, hmul]
      exact Nat.cast_le.mp this
    have hm1 : (m+1)*(m+1) = m^2 + 2*m + 1 := by ring
    rw [hn, hm1]
    omega

private lemma sp_split (d u v : ℕ) :
    (d*(u^2+2*v^2) + d*(((u:ℤ)^2 - 2*(v:ℤ)^2).natAbs) = 2*(d*u^2) ∧
     d*(u^2+2*v^2) - d*(((u:ℤ)^2 - 2*(v:ℤ)^2).natAbs) = 4*(d*v^2))
    ∨ (d*(u^2+2*v^2) + d*(((u:ℤ)^2 - 2*(v:ℤ)^2).natAbs) = 4*(d*v^2) ∧
       d*(u^2+2*v^2) - d*(((u:ℤ)^2 - 2*(v:ℤ)^2).natAbs) = 2*(d*u^2)) := by
  set S : ℤ := (u:ℤ)^2 - 2*(v:ℤ)^2 with hS
  set q : ℕ := S.natAbs with hq
  rcases le_or_gt (0:ℤ) S with h | h
  case inl =>
    left
    have hqz : (q:ℤ) = (u:ℤ)^2 - 2*(v:ℤ)^2 := by
      rw [hq, hS]; exact Int.natAbs_of_nonneg h
    have h1 : (u^2+2*v^2) + q = 2*u^2 := by
      apply Int.natCast_inj.mp
      push_cast
      rw [hqz]; ring
    have hle : q ≤ u^2 + 2*v^2 := by
      have : (q:ℤ) ≤ ((u^2+2*v^2 : ℕ):ℤ) := by push_cast; rw [hqz]; nlinarith [sq_nonneg (v:ℤ)]
      exact_mod_cast this
    have h2 : (u^2+2*v^2) - q = 4*v^2 := by
      apply Int.natCast_inj.mp
      rw [Nat.cast_sub hle]
      push_cast
      rw [hqz]; ring
    constructor
    · rw [← Nat.mul_add, h1]; ring
    · rw [← Nat.mul_sub_left_distrib, h2]; ring
  case inr =>
    right
    have hqz : (q:ℤ) = 2*(v:ℤ)^2 - (u:ℤ)^2 := by
      rw [hq, hS, ← Int.natAbs_neg, neg_sub]
      exact Int.natAbs_of_nonneg (by linarith)
    have h1 : (u^2+2*v^2) + q = 4*v^2 := by
      apply Int.natCast_inj.mp
      push_cast
      rw [hqz]; ring
    have hle : q ≤ u^2 + 2*v^2 := by
      have : (q:ℤ) ≤ ((u^2+2*v^2 : ℕ):ℤ) := by push_cast; rw [hqz]; nlinarith [sq_nonneg (u:ℤ)]
      exact_mod_cast this
    have h2 : (u^2+2*v^2) - q = 2*u^2 := by
      apply Int.natCast_inj.mp
      rw [Nat.cast_sub hle]
      push_cast
      rw [hqz]; ring
    constructor
    · rw [← Nat.mul_add, h1]; ring
    · rw [← Nat.mul_sub_left_distrib, h2]; ring

private lemma sp_mu_star_eq {d1 d2 a b : ℕ} (hd1 : mu_star d1) (hd2 : mu_star d2)
    (ha : Odd a) (hb : Odd b) (h : d1 * a^2 = d2 * b^2) : d1 = d2 := by
  have ha0 : 0 < a := ha.pos
  set g := Nat.gcd a b with hg
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hga ha0
  set a' := a / g
  set b' := b / g
  have haeq : a = g * a' := by rw [mul_comm, Nat.div_mul_cancel hga]
  have hbeq : b = g * b' := by rw [mul_comm, Nat.div_mul_cancel hgb]
  have hcop : a'.Coprime b' := Nat.coprime_div_gcd_div_gcd hg0
  have ha' : Odd a' := ha.of_dvd_nat (Nat.div_dvd_of_dvd hga)
  have hb' : Odd b' := hb.of_dvd_nat (Nat.div_dvd_of_dvd hgb)
  have h2 : d1 * a'^2 = d2 * b'^2 := by
    have hh : d1 * (g*a')^2 = d2*(g*b')^2 := by rw [← haeq, ← hbeq]; exact h
    have hg2 : (0:ℕ) < g^2 := pow_pos hg0 2
    nlinarith [hh, hg2]
  have hb'2dvd : b'^2 ∣ d1 := by
    have hcop' : (b'^2).Coprime (a'^2) := hcop.symm.pow 2 2
    apply hcop'.dvd_of_dvd_mul_left
    rw [mul_comm (a'^2) d1, h2]
    exact dvd_mul_left (b'^2) d2
  have ha'2dvd : a'^2 ∣ d2 := by
    have hcop' : (a'^2).Coprime (b'^2) := hcop.pow 2 2
    apply hcop'.dvd_of_dvd_mul_left
    rw [mul_comm (b'^2) d2, ← h2]
    exact dvd_mul_left (a'^2) d1
  have hb'1 : b' = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p ≠ 2 := by
      intro hp2eq
      rw [hp2eq] at hpdvd
      have hev : Even b' := by obtain ⟨k,hk⟩ := hpdvd; exact ⟨k, by rw [hk]; ring⟩
      exact (Nat.not_even_iff_odd).mpr hb' hev
    have : p^2 ∣ d1 := dvd_trans (pow_dvd_pow_of_dvd hpdvd 2) hb'2dvd
    exact hd1 p hp hp2 this
  have ha'1 : a' = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p ≠ 2 := by
      intro hp2eq
      rw [hp2eq] at hpdvd
      have hev : Even a' := by obtain ⟨k,hk⟩ := hpdvd; exact ⟨k, by rw [hk]; ring⟩
      exact (Nat.not_even_iff_odd).mpr ha' hev
    have : p^2 ∣ d2 := dvd_trans (pow_dvd_pow_of_dvd hpdvd 2) ha'2dvd
    exact hd2 p hp hp2 this
  rw [hb'1, ha'1] at h2
  simpa using h2

private lemma sp_parity (d1 d2 u1 u2 v1 v2 : ℕ)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hu1 : Odd u1) (hu2 : Odd u2)
    (e1 : d1*u1^2 = 2*(d2*v2^2)) (e2 : 2*(d1*v1^2) = d2*u2^2) : False := by
  have h1 : (d1:ℤ)*(u1:ℤ)^2 = 2*(d2:ℤ)*(v2:ℤ)^2 := by
    have hh : ((d1*u1^2 : ℕ):ℤ) = ((2*(d2*v2^2) : ℕ):ℤ) := by rw [e1]
    push_cast at hh ⊢
    linarith
  have h2 : 2*(d1:ℤ)*(v1:ℤ)^2 = (d2:ℤ)*(u2:ℤ)^2 := by
    have hh : ((2*(d1*v1^2) : ℕ):ℤ) = ((d2*u2^2 : ℕ):ℤ) := by rw [e2]
    push_cast at hh ⊢
    linarith
  have hmul : ((d1:ℤ)*(u1:ℤ)^2) * ((d2:ℤ)*(u2:ℤ)^2)
      = (2*(d2:ℤ)*(v2:ℤ)^2) * (2*(d1:ℤ)*(v1:ℤ)^2) := by rw [h1, h2]
  have key : ((u1:ℤ)*u2)^2 = (2*((v1:ℤ))*v2)^2 := by
    have hcancel : ((d1:ℤ))*((d2:ℤ))*(((u1:ℤ))*u2)^2
        = ((d1:ℤ))*((d2:ℤ))*(2*((v1:ℤ))*v2)^2 := by
      linear_combination hmul
    exact mul_left_cancel₀ (by positivity) hcancel
  have keyN : (u1*u2)^2 = (2*(v1*v2))^2 := by
    apply Int.natCast_inj.mp
    push_cast
    linarith [key]
  have hodd : Odd ((u1*u2)^2) := (hu1.mul hu2).pow
  have heven : Even ((2*(v1*v2))^2) := ⟨2*(v1*v2)^2, by ring⟩
  rw [← keyN] at heven
  exact (Nat.not_even_iff_odd).mpr hodd heven

/-- The parameterization map is injective on stein_param_set. -/
theorem stein_param_inj_on :
    Set.InjOn (fun (d, u, v) => d^2 * (u^4 + 4 * v^4)) stein_param_set := by
  rintro ⟨d1,u1,v1⟩ h1 ⟨d2,u2,v2⟩ h2 heq
  simp only [stein_param_set, Set.mem_setOf_eq] at h1 h2
  obtain ⟨hd1, hu1, hv1, ho1, hmu1, hin1⟩ := h1
  obtain ⟨hd2, hu2, hv2, ho2, hmu2, hin2⟩ := h2
  simp only at heq
  have hm1 := sp_sqrt d1 u1 v1 hd1 hin1
  have hm2 := sp_sqrt d2 u2 v2 hd2 hin2
  have hmeq : 2*d1*u1*v1 = 2*d2*u2*v2 := by rw [← hm1, ← hm2, heq]
  have hpeq : (d1 * (((u1:ℤ)^2 - 2*(v1:ℤ)^2).natAbs))^2
      = (d2 * (((u2:ℤ)^2 - 2*(v2:ℤ)^2).natAbs))^2 := by
    have a1 := sp_n_eq d1 u1 v1
    have a2 := sp_n_eq d2 u2 v2
    rw [a1] at heq
    rw [a2] at heq
    rw [hmeq] at heq
    linarith
  have hpq : d1 * (((u1:ℤ)^2 - 2*(v1:ℤ)^2).natAbs)
      = d2 * (((u2:ℤ)^2 - 2*(v2:ℤ)^2).natAbs) := sp_sq_inj hpeq
  have hqeq : d1*(u1^2+2*v1^2) = d2*(u2^2+2*v2^2) := by
    apply sp_sq_inj
    rw [sp_A_sq d1 u1 v1, sp_A_sq d2 u2 v2, heq, hmeq]
  have hsum : d1*(u1^2+2*v1^2) + d1*(((u1:ℤ)^2-2*(v1:ℤ)^2).natAbs)
      = d2*(u2^2+2*v2^2) + d2*(((u2:ℤ)^2-2*(v2:ℤ)^2).natAbs) := by rw [hqeq, hpq]
  have hdiff : d1*(u1^2+2*v1^2) - d1*(((u1:ℤ)^2-2*(v1:ℤ)^2).natAbs)
      = d2*(u2^2+2*v2^2) - d2*(((u2:ℤ)^2-2*(v2:ℤ)^2).natAbs) := by rw [hqeq, hpq]
  have key : d1*u1^2 = d2*u2^2 → (d1,u1,v1) = (d2,u2,v2) := by
    intro e1
    have hd : d1 = d2 := sp_mu_star_eq hmu1 hmu2 ho1 ho2 e1
    have hu : u1^2 = u2^2 := by rw [← hd] at e1; exact Nat.mul_left_cancel hd1 e1
    have hu' : u1 = u2 := sp_sq_inj hu
    have hv : v1 = v2 := by
      rw [hd, hu'] at hmeq
      exact Nat.mul_left_cancel (by positivity) hmeq
    rw [hd, hu', hv]
  rcases sp_split d1 u1 v1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
    rcases sp_split d2 u2 v2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
  · exact key (by omega)
  · have e1 : d1*u1^2 = 2*(d2*v2^2) := by omega
    have e2 : 2*(d1*v1^2) = d2*u2^2 := by omega
    exact absurd (sp_parity d1 d2 u1 u2 v1 v2 hd1 hd2 ho1 ho2 e1 e2) (not_false)
  · have e1 : d2*u2^2 = 2*(d1*v1^2) := by omega
    have e2 : 2*(d2*v2^2) = d1*u1^2 := by omega
    exact absurd (sp_parity d2 d1 u2 u1 v2 v1 hd2 hd1 ho2 ho1 e1 e2) (not_false)
  · exact key (by omega)
