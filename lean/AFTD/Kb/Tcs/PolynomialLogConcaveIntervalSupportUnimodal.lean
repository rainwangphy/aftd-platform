import AFTD.Prelude
import AFTD.Kb.Tcs.PolynomialIsUnimodal

/-!
# polynomial_log_concave_interval_support_unimodal

Topic: graphs   Node: 8d90093fe332

Provenance: helper lemma. Helper for tree_zero_forcing_poly_unimodal, via log-concavity of its coefficient sequence.

A natural-coefficient polynomial with log-concave coefficients and no internal zero coefficients is unimodal.
-/

private lemma polynomial_log_concave_interval_support_unimodal_halves
    (a : ℕ → ℕ) (m : ℕ)
    (hlo : ∀ i, i < m → a i ≤ a (i+1))
    (hhi : ∀ j, m ≤ j → a (j+1) ≤ a j) :
    ∃ m, (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧ (∀ i j, m ≤ i → i ≤ j → a j ≤ a i) := by
  refine ⟨m, ?_, ?_⟩
  · intro i j hij hjm
    have key : ∀ t, i ≤ t → t ≤ m → a i ≤ a t := by
      intro t hit
      induction t, hit using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ t hit ih =>
          intro htm
          have htm' : t ≤ m := le_trans (Nat.le_succ t) htm
          have hlt : t < m := Nat.lt_of_succ_le htm
          exact le_trans (ih htm') (hlo t hlt)
    exact key j hij hjm
  · intro i j hmi hij
    have key : ∀ t, i ≤ t → a t ≤ a i := by
      intro t hit
      induction t, hit using Nat.le_induction with
      | base => exact le_rfl
      | succ t hit ih =>
          have hmt : m ≤ t := le_trans hmi hit
          exact le_trans (hhi t hmt) ih
    exact key j hij

private lemma polynomial_log_concave_interval_support_unimodal_step (a : ℕ → ℕ)
    (hlc : ∀ k, a k * a (k + 2) ≤ a (k + 1) * a (k + 1))
    (k : ℕ) (hmono : a (k+1) ≤ a k) (hpos : 0 < a (k+1)) :
    a (k+2) ≤ a (k+1) := by
  have h1 : a (k+1) * a (k+2) ≤ a k * a (k+2) := Nat.mul_le_mul_right _ hmono
  have h2 : a k * a (k+2) ≤ a (k+1) * a (k+1) := hlc k
  have h3 : a (k+1) * a (k+2) ≤ a (k+1) * a (k+1) := le_trans h1 h2
  exact Nat.le_of_mul_le_mul_left h3 hpos

private lemma polynomial_log_concave_interval_support_unimodal_no_inc (a : ℕ → ℕ)
    (hlc : ∀ k, a k * a (k+2) ≤ a (k+1) * a (k+1))
    (hint : ∀ i j k, i ≤ j → j ≤ k → 0 < a i → 0 < a k → 0 < a j)
    {k k' : ℕ} (hkk' : k < k') (hdec : a (k+1) < a k) :
    a (k'+1) ≤ a k' := by
  have hstep := polynomial_log_concave_interval_support_unimodal_step a hlc
  have hkpos : 0 < a k := lt_of_le_of_lt (Nat.zero_le _) hdec
  by_cases hz : a (k'+1) = 0
  · rw [hz]; exact Nat.zero_le _
  · have hk'pos : 0 < a (k'+1) := Nat.pos_of_ne_zero hz
    have key : ∀ t, k ≤ t → t ≤ k' → a (t+1) ≤ a t := by
      intro t hkt
      induction t, hkt using Nat.le_induction with
      | base => intro _; exact le_of_lt hdec
      | succ t hkt ih =>
          intro htk'
          have htk : t ≤ k' := le_trans (Nat.le_succ t) htk'
          have ih' : a (t+1) ≤ a t := ih htk
          have hpos_t : 0 < a (t+1) := hint k (t+1) (k'+1) (by omega) (by omega) hkpos hk'pos
          exact hstep t ih' hpos_t
    exact key k' (le_of_lt hkk') le_rfl

theorem polynomial_log_concave_interval_support_unimodal (p : Polynomial ℕ) (hlc : ∀ k : ℕ, p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) * p.coeff (k + 1)) (hint : ∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < p.coeff i → 0 < p.coeff k → 0 < p.coeff j) : polynomial_is_unimodal p := by
  by_cases hp : p = 0
  · subst hp
    refine ⟨0, ?_, ?_⟩
    · rintro i j hij hj0
      have hj : j = 0 := by omega
      subst hj
      have hi : i = 0 := by omega
      subst hi
      simp
    · rintro i j hi0 hij
      simp
  · have hex : ∃ k, p.coeff (k+1) < p.coeff k := by
      refine ⟨p.natDegree, ?_⟩
      have h1 : p.coeff p.natDegree = p.leadingCoeff := Polynomial.coeff_natDegree
      have h2 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      have h3 : p.coeff (p.natDegree + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
      rw [h3, h1]
      exact Nat.pos_of_ne_zero h2
    let m := Nat.find hex
    have hm : p.coeff (m+1) < p.coeff m := Nat.find_spec hex
    exact polynomial_log_concave_interval_support_unimodal_halves p.coeff m
      (fun i hi => le_of_not_gt (Nat.find_min hex hi))
      (fun j hj => by
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact polynomial_log_concave_interval_support_unimodal_no_inc p.coeff hlc hint hlt hm
        · subst heq; exact le_of_lt hm)
