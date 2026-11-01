import AFTD.Prelude
import AFTD.Kb.NumberTheory.FourierThresholdNu
import AFTD.Kb.NumberTheory.ArithmeticFourierBound
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.G

/-!
# fourier_threshold_nu_odd_ge_arithmetic_bound

Topic: elementary_number_theory   Node: d4ca4b012d43

Provenance: formalization of a published result. Source: arXiv:2610.38447, Section 5.3, Lemma 5.1

For every integer m >= 1, the arithmetic bound lambda_{2m+1} is a lower bound on the Fourier threshold nu(2m+1).
-/

namespace ft716

open Finset

/-- the character value in ZMod 3 -/
def chi {d : ℕ} (u x : Fin d → ZMod 2) : ZMod 3 := if ∑ i, u i * x i = 0 then 1 else -1

def fh {d : ℕ} (f : (Fin d → ZMod 2) → ZMod 3) (u : Fin d → ZMod 2) : ZMod 3 := ∑ x, f x * chi u x

theorem dot_add_right {d : ℕ} (u x y : Fin d → ZMod 2) :
    ∑ i, u i * (x + y) i = ∑ i, u i * x i + ∑ i, u i * y i := by
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => by simp [mul_add])

theorem dot_comm {d : ℕ} (u x : Fin d → ZMod 2) : ∑ i, u i * x i = ∑ i, x i * u i :=
  Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem chi_of (a b : ZMod 2) : (if a + b = 0 then (1 : ZMod 3) else -1) =
    (if a = 0 then 1 else -1) * (if b = 0 then 1 else -1) := by
  revert a b; decide

theorem chi_mul {d : ℕ} (u x y : Fin d → ZMod 2) : chi u (x + y) = chi u x * chi u y := by
  unfold chi; rw [dot_add_right]; exact chi_of _ _

theorem chi_comm {d : ℕ} (u x : Fin d → ZMod 2) : chi u x = chi x u := by
  unfold chi; rw [dot_comm]

theorem chi_add_left {d : ℕ} (v u y : Fin d → ZMod 2) : chi (v + u) y = chi v y * chi u y := by
  rw [chi_comm, chi_mul, chi_comm y v, chi_comm y u]

theorem chi_zero {d : ℕ} (u : Fin d → ZMod 2) : chi u 0 = 1 := by simp [chi]

/-- character sums -/
theorem chi_sum {d : ℕ} (z : Fin d → ZMod 2) :
    ∑ u : Fin d → ZMod 2, chi u z = if z = 0 then (2 : ZMod 3) ^ d else 0 := by
  classical
  split_ifs with hz
  · subst hz; simp [chi_zero, Fintype.card_fun, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h; push Not at h; exact hz (funext h)
    have hzi : z i = 1 := by
      have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact this _ hi
    let e : Fin d → ZMod 2 := Pi.single i 1
    have he : ∑ j, e j * z j = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [e, hzi]
      · intro j _ hj; simp [e, Pi.single_apply, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hflip : ∀ u, chi (u + e) z = - chi u z := by
      intro u
      rw [chi_add_left]
      simp only [chi, he]
      split_ifs <;> simp_all
    have hS : ∑ u : Fin d → ZMod 2, chi u z = - ∑ u : Fin d → ZMod 2, chi u z := by
      rw [← Finset.sum_neg_distrib]
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight e)]
      exact Finset.sum_congr rfl (fun u _ => by simp [hflip])
    have h2 : (2 : ZMod 3) * ∑ u : Fin d → ZMod 2, chi u z = 0 := by
      rw [two_mul]; nth_rewrite 1 [hS]; ring
    have h2u : IsUnit (2 : ZMod 3) := by decide
    exact (h2u.mul_right_eq_zero).mp h2

theorem sq_of_ne (z : ZMod 3) : z ^ 2 = if z = 0 then 0 else 1 := by revert z; decide

/-- convolution identity -/
theorem conv {d : ℕ} (f : (Fin d → ZMod 2) → ZMod 3) (hf : ∀ x, f x = 0 ↔ x = 0)
    (u : Fin d → ZMod 2) :
    ∑ v, fh f v * fh f (v + u) = (2 : ZMod 3) ^ d * ((if u = 0 then (2 : ZMod 3) ^ d else 0) - 1) := by
  classical
  have step1 : ∑ v, fh f v * fh f (v + u) =
      ∑ x, ∑ y, f x * f y * chi u x * ∑ v, chi v (x + y) := by
    calc ∑ v, fh f v * fh f (v + u)
        = ∑ v, ∑ x, ∑ y, f x * f y * chi u x * chi v (x + y) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          simp only [fh, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
          rw [chi_add_left, chi_mul]; ring
      _ = ∑ x, ∑ y, f x * f y * chi u x * ∑ v, chi v (x + y) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
  rw [step1]
  simp only [chi_sum]
  have hxy : ∀ x y : Fin d → ZMod 2, (x + y = 0) ↔ y = x := by
    intro x y
    constructor
    · intro h; funext i; have := congrFun h i; simp at this
      have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
      exact key _ _ this
    · rintro rfl; funext i; simp
      have key : ∀ a : ZMod 2, a + a = 0 := by decide
      exact key _
  have step2 : ∀ x, ∑ y, f x * f y * chi u x * (if x + y = 0 then (2 : ZMod 3) ^ d else 0) =
      (2 : ZMod 3) ^ d * (f x ^ 2 * chi u x) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [if_pos ((hxy x x).mpr rfl)]; ring
    · intro y _ hyx; rw [if_neg (fun h => hyx ((hxy x y).mp h))]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  simp only [step2, ← Finset.mul_sum, sq_of_ne, ite_mul, zero_mul, one_mul]
  congr 1
  have : ∑ x : Fin d → ZMod 2, (if f x = 0 then 0 else chi u x) =
      ∑ x : Fin d → ZMod 2, chi u x - chi u 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin d → ZMod 2))]
    rw [show (if f 0 = 0 then 0 else chi u 0) = 0 by simp [(hf 0).mpr rfl]]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin d → ZMod 2))]
    simp only [add_zero, add_sub_cancel_right]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [if_neg (fun h => (Finset.mem_erase.mp hx).1 ((hf x).mp h))]
  rw [this, chi_zero]
  simp only [chi_comm u, chi_sum]

/-- inversion at zero -/
theorem sum_fh {d : ℕ} (f : (Fin d → ZMod 2) → ZMod 3) (hf : ∀ x, f x = 0 ↔ x = 0) :
    ∑ v, fh f v = 0 := by
  classical
  simp only [fh]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, chi_comm _ _]
  rw [Finset.sum_eq_single (0 : Fin d → ZMod 2)]
  · simp [(hf 0).mpr rfl]
  · intro x _ hx
    have : ∑ v : Fin d → ZMod 2, chi x v = 0 := by
      rw [show (∑ v : Fin d → ZMod 2, chi x v) = ∑ v : Fin d → ZMod 2, chi v x from
        Finset.sum_congr rfl (fun v _ => chi_comm x v), chi_sum, if_neg hx]
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- integer lift -/
def lift3 (z : ZMod 3) : ℤ := if z = 0 then 0 else if z = 1 then 1 else -1

theorem lift3_cast (z : ZMod 3) : ((lift3 z : ℤ) : ZMod 3) = z := by
  revert z; unfold lift3; decide

theorem lift3_ne (z : ZMod 3) : lift3 z ≠ 0 ↔ z ≠ 0 := by
  revert z; unfold lift3; decide

theorem lift3_vals (z : ZMod 3) : lift3 z = 0 ∨ lift3 z = 1 ∨ lift3 z = -1 := by
  revert z; unfold lift3; decide

theorem lift3_sq (z : ZMod 3) : lift3 z * lift3 z = if lift3 z ≠ 0 then 1 else 0 := by
  revert z; unfold lift3; decide

theorem two_pow_odd (m : ℕ) : (2 : ZMod 3) ^ (2 * m + 1) = 2 := by
  rw [pow_succ, pow_mul]; norm_num
  have : (4 : ZMod 3) = 1 := by decide
  simp [this]

theorem zmod3_one_iff (z : ℤ) : ((z : ℤ) : ZMod 3) = 1 → z % 3 = 1 := by
  intro h
  have h' : (((z - 1 : ℤ)) : ZMod 3) = 0 := by push_cast; rw [h]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  omega

theorem zmod3_two_iff (z : ℤ) : ((z : ℤ) : ZMod 3) = 2 → z % 3 = 2 := by
  intro h
  have h' : (((z - 2 : ℤ)) : ZMod 3) = 0 := by push_cast; rw [h]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  omega

theorem zmod3_zero_iff (z : ℤ) : ((z : ℤ) : ZMod 3) = 0 → z % 3 = 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  omega

theorem vadd_cancel {d : ℕ} (v u : Fin d → ZMod 2) : v + u + u = v := by
  funext i; simp only [Pi.add_apply]
  have key : ∀ a b : ZMod 2, a + b + b = a := by decide
  exact key _ _

theorem vadd_ne {d : ℕ} (v u : Fin d → ZMod 2) (hu : u ≠ 0) : v + u ≠ v := by
  intro h; apply hu; funext i; have := congrFun h i; simp only [Pi.add_apply] at this
  have key : ∀ a b : ZMod 2, a + b = a → b = 0 := by decide
  exact key _ _ this

/-- the main inequality for one admissible f, in ℤ -/
theorem main_ineq (d : ℕ) (h2d : (2 : ZMod 3) ^ d = 2)
    (f : (Fin d → ZMod 2) → ZMod 3) (hf : ∀ x, f x = 0 ↔ x = 0) :
    let a : (Fin d → ZMod 2) → ℤ := fun v => lift3 (fh f v)
    let n : ℤ := ∑ v, (if a v ≠ 0 then 1 else 0)
    n % 3 = 2 ∧ 8 * ((2 : ℤ) ^ d - 1) + 2 * n + (if n % 2 = 1 then 9 else 0) ≤ 3 * n ^ 2 := by
  classical
  intro a n
  let KZ : (Fin d → ZMod 2) → ℤ := fun u => ∑ v, a v * a (v + u)
  let N : (Fin d → ZMod 2) → ℤ := fun u => ∑ v, (if a v * a (v + u) ≠ 0 then 1 else 0)
  let σ : ℤ := ∑ v, a v
  have hKZc : ∀ u, ((KZ u : ℤ) : ZMod 3) = (2 : ZMod 3) ^ d * ((if u = 0 then (2 : ZMod 3) ^ d else 0) - 1) := by
    intro u; simp only [KZ, a]; push_cast; simp only [lift3_cast]; exact conv f hf u
  have hKZ0 : KZ 0 = n := by
    simp only [KZ, n, add_zero]; exact Finset.sum_congr rfl (fun v _ => lift3_sq _)
  have hn3 : n % 3 = 2 := by
    apply zmod3_two_iff; rw [← hKZ0, hKZc 0, if_pos rfl, h2d]; decide
  have hKZu : ∀ u, u ≠ 0 → KZ u % 3 = 1 := by
    intro u hu; apply zmod3_one_iff; rw [hKZc u, if_neg hu, h2d]; decide
  have hσ3 : σ % 3 = 0 := by
    apply zmod3_zero_iff; simp only [σ, a]; push_cast; simp only [lift3_cast]; exact sum_fh f hf
  have hσ2 : (σ - n) % 2 = 0 := by
    have : σ - n = ∑ v, (a v - if a v ≠ 0 then 1 else 0) := by
      simp only [σ, n, Finset.sum_sub_distrib]
    rw [this]
    apply Int.emod_eq_zero_of_dvd
    apply Finset.dvd_sum
    intro v _
    rcases lift3_vals (fh f v) with h | h | h <;> simp [a, h]
  have hsumKZ : ∑ u, KZ u = σ ^ 2 := by
    simp only [KZ]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    have : ∀ v, ∑ u, a (v + u) = σ := fun v => Equiv.sum_comp (Equiv.addLeft v) a
    simp only [this, ← Finset.sum_mul, σ]; ring
  have hsumN : ∑ u, N u = n ^ 2 := by
    simp only [N, n]
    have hsplit : ∀ v u, (if a v * a (v + u) ≠ 0 then (1 : ℤ) else 0) =
        (if a v ≠ 0 then 1 else 0) * (if a (v + u) ≠ 0 then 1 else 0) := by
      intro v u; by_cases h1 : a v = 0 <;> by_cases h2 : a (v + u) = 0 <;> simp [h1, h2]
    simp only [hsplit]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    have : ∀ v, ∑ u, (if a (v + u) ≠ 0 then (1 : ℤ) else 0) = ∑ w, (if a w ≠ 0 then 1 else 0) :=
      fun v => Equiv.sum_comp (Equiv.addLeft v) (fun w => if a w ≠ 0 then (1 : ℤ) else 0)
    simp only [this, ← Finset.sum_mul]; ring
  have hN0 : N 0 = n := by simp only [N, n, add_zero]; exact Finset.sum_congr rfl (fun v _ => by
    by_cases h : a v = 0 <;> simp [h])
  -- per nonzero shift
  have hper : ∀ u, u ≠ 0 → 8 ≤ 3 * N u - KZ u := by
    intro u hu
    let t : (Fin d → ZMod 2) → ℤ := fun v => a v * a (v + u)
    have ht : ∀ v, t (v + u) = t v := by intro v; simp only [t, vadd_cancel]; ring
    have htv : ∀ v, t v = 0 ∨ t v = 1 ∨ t v = -1 := by
      intro v; simp only [t, a]
      rcases lift3_vals (fh f v) with h | h | h <;> rcases lift3_vals (fh f (v + u)) with h' | h' | h' <;>
        simp [h, h']
    let g : (Fin d → ZMod 2) → ℤ := fun v => 3 * (if t v ≠ 0 then 1 else 0) - t v
    have hg : 3 * N u - KZ u = ∑ v, g v := by
      simp only [g, N, KZ, t, Finset.sum_sub_distrib, Finset.mul_sum]
    have hg0 : ∀ v, 0 ≤ g v := by
      intro v; rcases htv v with h | h | h <;> simp [g, h]
    have hpair : ∀ v, g v + g (v + u) ≤ ∑ w, g w := by
      intro v
      have hsub : ({v, v + u} : Finset _) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hg0 w)
      rwa [Finset.sum_pair (vadd_ne v u hu).symm] at this
    rw [hg]
    by_cases hneg : ∃ v, t v = -1
    · obtain ⟨v, hv⟩ := hneg
      have h1 : g v = 4 := by simp [g, hv]
      have h2 : g (v + u) = 4 := by simp [g, ht, hv]
      have := hpair v; omega
    · push Not at hneg
      have h01 : ∀ v, t v = 0 ∨ t v = 1 := fun v => by
        rcases htv v with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h (hneg v)
      have hKN : KZ u = N u := by
        simp only [KZ, N]; refine Finset.sum_congr rfl (fun v _ => ?_)
        rcases h01 v with h | h <;> simp only [t] at h <;> simp [h]
      have hmod := hKZu u hu
      have hne : KZ u ≠ 0 := by intro h; rw [h] at hmod; norm_num at hmod
      obtain ⟨v, hv⟩ : ∃ v, t v = 1 := by
        by_contra hc; push Not at hc
        apply hne; simp only [KZ]; exact Finset.sum_eq_zero (fun v _ => by
          rcases h01 v with h | h
          · exact h
          · exact absurd h (hc v))
      have hgv : g v = 2 := by simp [g, hv]
      have hgv' : g (v + u) = 2 := by simp [g, ht, hv]
      have hge := hpair v
      have hgsum : ∑ w, g w = 2 * N u := by rw [← hg, hKN]; ring
      omega
  -- sum over shifts
  have htot : ∑ u, (3 * N u - KZ u) = 3 * n ^ 2 - σ ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumN, hsumKZ]
  have hrest : ∑ u ∈ Finset.univ.erase 0, (3 * N u - KZ u) ≥
      ∑ u ∈ Finset.univ.erase (0 : Fin d → ZMod 2), (8 : ℤ) :=
    Finset.sum_le_sum (fun u hu => hper u (Finset.mem_erase.mp hu).1)
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin] at hrest
  have hsplit0 := Finset.sum_erase_add Finset.univ (fun u => 3 * N u - KZ u) (Finset.mem_univ 0)
  rw [htot, hN0, hKZ0] at hsplit0
  have hpow : (1 : ℤ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hcast : ((2 ^ d - 1 : ℕ) : ℤ) = (2 : ℤ) ^ d - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; ring
  simp only [nsmul_eq_mul, hcast] at hrest
  refine ⟨hn3, ?_⟩
  split_ifs with hodd
  · -- n odd, so σ odd and divisible by 3: σ² ≥ 9
    have hσodd : σ % 2 = 1 := by omega
    obtain ⟨k, hk⟩ : (3 : ℤ) ∣ σ := Int.dvd_of_emod_eq_zero hσ3
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
    have hk2 : 1 ≤ k ^ 2 := by
      have := pow_pos (abs_pos.mpr hk0) 2
      rw [sq_abs] at this
      omega
    have : 9 ≤ σ ^ 2 := by rw [hk]; nlinarith
    nlinarith
  · nlinarith [sq_nonneg σ]

theorem card_mem (m : ℕ) (f : (Fin (2 * m + 1) → ZMod 2) → ZMod 3) (hf : ∀ x, f x = 0 ↔ x = 0) :
    (Finset.filter (fun (u : Fin (2 * m + 1) → ZMod 2) =>
      (-1 : ZMod 3) ^ (2 * m + 1) * ∑ x : Fin (2 * m + 1) → ZMod 2,
        f x * (if ∑ i, u i * x i = 0 then 1 else -1) ≠ 0) Finset.univ).card ∈
    {n : ℕ | n % 3 = 2 ∧ 8 * (2 ^ (2 * m + 1) - 1) + 2 * n + (if n % 2 = 1 then 9 else 0) ≤ 3 * n ^ 2} := by
  classical
  have key := main_ineq (2 * m + 1) (two_pow_odd m) f hf
  dsimp only at key
  set c := (Finset.filter (fun (u : Fin (2 * m + 1) → ZMod 2) =>
      (-1 : ZMod 3) ^ (2 * m + 1) * ∑ x : Fin (2 * m + 1) → ZMod 2,
        f x * (if ∑ i, u i * x i = 0 then 1 else -1) ≠ 0) Finset.univ).card with hc
  have hcount : (∑ v : Fin (2 * m + 1) → ZMod 2, (if lift3 (fh f v) ≠ 0 then (1 : ℤ) else 0)) = (c : ℤ) := by
    rw [hc, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hu : (-1 : ZMod 3) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (by decide)
    have : (lift3 (fh f v) ≠ 0) ↔ ((-1 : ZMod 3) ^ (2 * m + 1) * ∑ x : Fin (2 * m + 1) → ZMod 2,
        f x * (if ∑ i, v i * x i = 0 then 1 else -1) ≠ 0) := by
      rw [lift3_ne, mul_ne_zero_iff, and_iff_right hu]; rfl
    simp only [this]
  rw [hcount] at key
  obtain ⟨h1, h2⟩ := key
  refine ⟨by omega, ?_⟩
  have hp : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  by_cases hodd : c % 2 = 1
  · rw [if_pos hodd]
    rw [if_pos (by omega)] at h2
    zify [hp]; push_cast; linarith
  · rw [if_neg hodd]
    rw [if_neg (by omega)] at h2
    zify [hp]; push_cast; linarith

end ft716

/-- The arithmetic lower bound on the odd-dimensional Fourier threshold nu(2m+1). -/
theorem fourier_threshold_nu_odd_ge_arithmetic_bound (m : ℕ) (hm : 1 ≤ m) :
    arithmetic_fourier_bound (2 * m + 1) ≤ fourier_threshold_nu (2 * m + 1) := by
  classical
  unfold fourier_threshold_nu
  rw [Finset.le_fold_min]
  constructor
  · -- 2^d itself lies in the defining set
    have hmem : 2 ^ (2 * m + 1) ∈ {n : ℕ | n % 3 = 2 ∧ 8 * (2 ^ (2 * m + 1) - 1) + 2 * n +
        (if n % 2 = 1 then 9 else 0) ≤ 3 * n ^ 2} := by
      have h3 : 2 ^ (2 * m + 1) % 3 = 2 := by
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
      have h2 : 2 ^ (2 * m + 1) % 2 = 0 := by
        rw [pow_succ]; simp
      refine ⟨h3, ?_⟩
      rw [if_neg (by omega)]
      have hp : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
      have hq : 2 ≤ 2 ^ (2 * m + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      zify [hp]; nlinarith
    exact (Nat.sInf_le hmem).trans (Nat.le_succ _)
  · intro f hf
    rw [Finset.mem_filter] at hf
    exact Nat.sInf_le (ft716.card_mem m f hf.2)
