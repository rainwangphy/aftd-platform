import AFTD.Prelude
import AFTD.Kb.Tcs.IsSignedDictator
import AFTD.Kb.Tcs.DictatorDist
import AFTD.Kb.Tcs.HellingerZ
import AFTD.Kb.Tcs.NoiseOperator

/-!
# antipodal_hellinger_signed_dictator_equality

Topic: information   Node: 955e769f0271

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:176

For every real number ρ with 0 < ρ < 1, every natural number n with 0 < n, and every signed dictator g : (Fin n → Bool) → ℝ satisfying is_signed_dictator n g, the Hellinger affinity satisfies hellinger_Z n ρ g = Real.sqrt (1 - ρ ^ 2) and the dictator distance satisfies dictator_dist n g = 0.
-/

open scoped BigOperators

private lemma antipodal_hellinger_signed_dictator_equality_wt {n : ℕ} {ρ : ℝ} (x y : Fin n → Bool) :
    ∏ j, (if x j = y j then (1 + ρ) / 2 else (1 - ρ) / 2)
      = ((1 + ρ) / 2) ^ (n - hammingDist x y) * ((1 - ρ) / 2) ^ hammingDist x y := by
  have hhd : hammingDist x y = (Finset.univ.filter (fun j => ¬ x j = y j)).card := rfl
  rw [Finset.prod_ite]
  rw [Finset.prod_const, Finset.prod_const]
  have hcard : (Finset.filter (fun j => x j = y j) (Finset.univ : Finset (Fin n))).card
      + (Finset.univ.filter (fun j => ¬ x j = y j)).card = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hsub : n - (Finset.univ.filter (fun j => ¬ x j = y j)).card
      = (Finset.filter (fun j => x j = y j) (Finset.univ : Finset (Fin n))).card := by omega
  rw [hhd, hsub]

private lemma antipodal_hellinger_signed_dictator_equality_noise_eq_sum_prod {n : ℕ} {ρ : ℝ}
    (f : (Fin n → Bool) → ℝ) (y : Fin n → Bool) :
    noise_operator n ρ f y
      = ∑ x, (∏ j, (if x j = y j then (1 + ρ) / 2 else (1 - ρ) / 2)) * f x := by
  unfold noise_operator
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [antipodal_hellinger_signed_dictator_equality_wt x y]

private lemma antipodal_hellinger_signed_dictator_equality_noise_dictator {n : ℕ} {ρ s : ℝ}
    {i : Fin n} (y : Fin n → Bool) :
    noise_operator n ρ (fun x => s * (if x i = true then -1 else 1)) y
      = ρ * (s * (if y i = true then -1 else 1)) := by
  rw [antipodal_hellinger_signed_dictator_equality_noise_eq_sum_prod]
  have hterm : ∀ x : Fin n → Bool,
      (∏ j, (if x j = y j then (1 + ρ) / 2 else (1 - ρ) / 2)) * (s * (if x i = true then -1 else 1))
      = s * ∏ j, ((if x j = y j then (1 + ρ) / 2 else (1 - ρ) / 2) *
            (if j = i then (if x j = true then -1 else 1) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib]
    have hsingle : (∏ j, if j = i then (if x j = true then -1 else 1) else (1 : ℝ))
        = (if x i = true then -1 else 1) := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hsingle]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum]
  have hps : (∏ j : Fin n, ∑ c : Bool, ((if c = y j then (1 + ρ) / 2 else (1 - ρ) / 2) *
        (if j = i then (if c = true then -1 else 1) else 1)))
      = ∑ x : Fin n → Bool, ∏ j : Fin n, ((if x j = y j then (1 + ρ) / 2 else (1 - ρ) / 2) *
        (if j = i then (if x j = true then -1 else 1) else 1)) :=
    Fintype.prod_sum _
  rw [← hps]
  have hfactor : ∀ j : Fin n,
      (∑ c : Bool, ((if c = y j then (1 + ρ) / 2 else (1 - ρ) / 2) *
        (if j = i then (if c = true then -1 else 1) else 1)))
      = if j = i then ρ * (if y i = true then -1 else 1) else 1 := by
    intro j
    rw [Fintype.sum_bool]
    by_cases hj : j = i
    · subst hj
      cases hy : y j <;> simp <;> ring
    · simp [hj]
      cases hy : y j <;> simp <;> ring
  simp only [hfactor]
  rw [Finset.prod_eq_single i]
  · by_cases hyi : y i = true <;> simp [hyi] <;> ring
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma antipodal_hellinger_signed_dictator_equality_hellinger {n : ℕ} {ρ : ℝ}
    {g : (Fin n → Bool) → ℝ} {i : Fin n} {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hg : ∀ x, g x = s * (if x i = true then -1 else 1)) :
    hellinger_Z n ρ g = Real.sqrt (1 - ρ ^ 2) := by
  have hgfun : g = fun x => s * (if x i = true then -1 else 1) := funext hg
  have hsq : ∀ y : Fin n → Bool, noise_operator n ρ g y ^ 2 = ρ ^ 2 := by
    intro y
    rw [hgfun, antipodal_hellinger_signed_dictator_equality_noise_dictator]
    rcases hs with h | h
    · rw [h]; by_cases hb : y i = true <;> simp [hb]
    · rw [h]; by_cases hb : y i = true <;> simp [hb]
  unfold hellinger_Z
  simp only [hsq]
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_pow]
  norm_num

private lemma antipodal_hellinger_signed_dictator_equality_dist_self {n : ℕ}
    {g : (Fin n → Bool) → ℝ} (hg : is_signed_dictator n g) :
    dictator_dist n g = 0 := by
  set D : ((Fin n → Bool) → ℝ) → ((Fin n → Bool) → ℝ) → ℝ :=
    fun f h => 1 / 2 ^ n * ∑ x : Fin n → Bool, if f x ≠ h x then (1:ℝ) else 0 with hD
  have hDnn : ∀ f h, 0 ≤ D f h := by
    intro f h
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun x _ => by split_ifs <;> norm_num))
  have hdd : dictator_dist n g = ⨅ d, ⨅ (_ : is_signed_dictator n d), D g d := rfl
  have hupper : dictator_dist n g ≤ 0 := by
    rw [hdd]
    have hbd : BddBelow (Set.range (fun d : (Fin n → Bool) → ℝ =>
        ⨅ (_ : is_signed_dictator n d), D g d)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨d, rfl⟩
      exact Real.iInf_nonneg (fun hd => hDnn g d)
    have h1 := ciInf_le hbd g
    rw [ciInf_pos hg] at h1
    have hzero : D g g = 0 := by simp [D]
    rw [hzero] at h1
    exact h1
  have hlower : 0 ≤ dictator_dist n g := by
    rw [hdd]
    exact Real.iInf_nonneg (fun d => Real.iInf_nonneg (fun hd => hDnn g d))
  exact le_antisymm hupper hlower

/-- Signed dictators attain equality Z_rho(g) = sqrt(1 - rho^2) and have dictator distance zero. -/
theorem antipodal_hellinger_signed_dictator_equality (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (n : ℕ) (hn : 0 < n) (g : (Fin n → Bool) → ℝ) (hg : is_signed_dictator n g) :
    hellinger_Z n ρ g = Real.sqrt (1 - ρ ^ 2) ∧ dictator_dist n g = 0 := by
  obtain ⟨i, s, hs, hgx⟩ := hg
  exact ⟨antipodal_hellinger_signed_dictator_equality_hellinger hs hgx,
    antipodal_hellinger_signed_dictator_equality_dist_self ⟨i, s, hs, hgx⟩⟩
