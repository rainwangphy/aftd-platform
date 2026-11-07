import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissibleInflectionSet
import AFTD.Kb.Tcs.PermSecondDerivative
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.PermInflectionSet

/-!
# op_686_single_element_admissible

Topic: combinatorics   Node: 189094cd2542

Provenance: formalization of a published result. Source: arXiv:2610.38237, Corollary 5.15

For all natural numbers k, m : ℕ satisfying 2 ≤ k and k < m, the single-element set {(k, m)} is an admissible inflection set (is_admissible_inflection_set {(k, m)}).
-/

def op_686_single_element_admissible_gadget_val (k m t : ℕ) : ℕ :=
  if t < k then t
  else if t < m then 2 * t - k + 1
  else 4 * m - k - 2 - 2 * t

theorem op_686_single_element_admissible_gadget_val_lt (k m t : ℕ) (hk : 2 ≤ k) (hkm : k < m) (ht : t < 2 * m - k) :
    op_686_single_element_admissible_gadget_val k m t < 2 * m - k := by
  unfold op_686_single_element_admissible_gadget_val; split_ifs <;> omega

theorem op_686_single_element_admissible_gadget_val_inj (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    ∀ t1 t2 : ℕ, t1 < 2 * m - k → t2 < 2 * m - k →
      op_686_single_element_admissible_gadget_val k m t1 = op_686_single_element_admissible_gadget_val k m t2 → t1 = t2 := by
  intro t1 t2 ht1 ht2 h
  unfold op_686_single_element_admissible_gadget_val at h
  split_ifs at h <;> omega

def op_686_single_element_admissible_gadget_fn (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    Fin (2 * m - k) → Fin (2 * m - k) := fun t =>
  ⟨op_686_single_element_admissible_gadget_val k m t.1,
   op_686_single_element_admissible_gadget_val_lt k m t.1 hk hkm t.2⟩

theorem op_686_single_element_admissible_gadget_fn_injective (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    Function.Injective (op_686_single_element_admissible_gadget_fn k m hk hkm) := by
  intro a b hab
  apply Fin.ext
  have h := congr_arg Fin.val hab
  exact op_686_single_element_admissible_gadget_val_inj k m hk hkm a.1 b.1 a.2 b.2 h

noncomputable def op_686_single_element_admissible_gadget_perm (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    Equiv.Perm (Fin (2 * m - k)) :=
  Equiv.ofBijective (op_686_single_element_admissible_gadget_fn k m hk hkm)
    ((op_686_single_element_admissible_gadget_fn_injective k m hk hkm).bijective_of_finite)

theorem op_686_single_element_admissible_gadget_d_eq (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) (ℓ : ℕ)
    (hℓ : 2 ≤ ℓ ∧ ℓ ≤ 2 * m - k - 1) :
    perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) ℓ =
      (op_686_single_element_admissible_gadget_val k m ℓ : ℤ) +
      (op_686_single_element_admissible_gadget_val k m (ℓ - 2) : ℤ) -
      2 * (op_686_single_element_admissible_gadget_val k m (ℓ - 1) : ℤ) := by
  unfold perm_second_derivative
  split_ifs
  rfl

theorem op_686_single_element_admissible_gadget_d_pos (k m ℓ : ℕ) (hk : 2 ≤ k) (hkm : k < m) (hℓ : 2 ≤ ℓ ∧ ℓ ≤ 2 * m - k - 1) :
    0 < (op_686_single_element_admissible_gadget_val k m ℓ : ℤ) +
        (op_686_single_element_admissible_gadget_val k m (ℓ - 2) : ℤ) -
        2 * (op_686_single_element_admissible_gadget_val k m (ℓ - 1) : ℤ) ↔ ℓ = k := by
  unfold op_686_single_element_admissible_gadget_val
  split_ifs <;> omega

theorem op_686_single_element_admissible_gadget_d_k (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    (op_686_single_element_admissible_gadget_val k m k : ℤ) +
    (op_686_single_element_admissible_gadget_val k m (k - 2) : ℤ) -
    2 * (op_686_single_element_admissible_gadget_val k m (k - 1) : ℤ) = 1 := by
  unfold op_686_single_element_admissible_gadget_val
  split_ifs <;> omega

theorem op_686_single_element_admissible_gadget_d_m (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    (op_686_single_element_admissible_gadget_val k m m : ℤ) +
    (op_686_single_element_admissible_gadget_val k m (m - 2) : ℤ) -
    2 * (op_686_single_element_admissible_gadget_val k m (m - 1) : ℤ) = -3 := by
  unfold op_686_single_element_admissible_gadget_val
  split_ifs <;> omega

theorem op_686_single_element_admissible_gadget_d_zero (k m ℓ : ℕ) (hk : 2 ≤ k) (hℓ : k < ℓ ∧ ℓ < m) :
    (op_686_single_element_admissible_gadget_val k m ℓ : ℤ) +
    (op_686_single_element_admissible_gadget_val k m (ℓ - 2) : ℤ) -
    2 * (op_686_single_element_admissible_gadget_val k m (ℓ - 1) : ℤ) = 0 := by
  unfold op_686_single_element_admissible_gadget_val
  split_ifs <;> omega

theorem op_686_single_element_admissible_gadget_d_lt_k_zero (k m ℓ : ℕ) (hℓ : 2 ≤ ℓ ∧ ℓ < k) :
    (op_686_single_element_admissible_gadget_val k m ℓ : ℤ) +
    (op_686_single_element_admissible_gadget_val k m (ℓ - 2) : ℤ) -
    2 * (op_686_single_element_admissible_gadget_val k m (ℓ - 1) : ℤ) = 0 := by
  unfold op_686_single_element_admissible_gadget_val
  split_ifs <;> omega

theorem op_686_single_element_admissible_gadget_perm_inflection_set (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    perm_inflection_set (op_686_single_element_admissible_gadget_perm k m hk hkm) = {(k, m)} := by
  let n := 2 * m - k
  have hkn : 2 ≤ k ∧ k ≤ n - 1 := by dsimp [n]; omega
  have hmn : 2 ≤ m ∧ m ≤ n - 1 := by dsimp [n]; omega
  have hdk : perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) k = 1 := by
    rw [op_686_single_element_admissible_gadget_d_eq k m hk hkm k hkn]
    exact op_686_single_element_admissible_gadget_d_k k m hk hkm
  have hdm : perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) m = -3 := by
    rw [op_686_single_element_admissible_gadget_d_eq k m hk hkm m hmn]
    exact op_686_single_element_admissible_gadget_d_m k m hk hkm
  have hd_zero : ∀ ℓ ∈ Finset.Ioo k m,
      perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) ℓ = 0 := by
    intro ℓ hℓ
    rw [Finset.mem_Ioo] at hℓ
    have hℓn : 2 ≤ ℓ ∧ ℓ ≤ n - 1 := by dsimp [n]; omega
    rw [op_686_single_element_admissible_gadget_d_eq k m hk hkm ℓ hℓn]
    exact op_686_single_element_admissible_gadget_d_zero k m ℓ hk hℓ
  have h_mem : (k, m) ∈ perm_inflection_set (op_686_single_element_admissible_gadget_perm k m hk hkm) := by
    unfold perm_inflection_set
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hkm, ?_, hd_zero⟩
    · rw [Finset.mem_Icc]; exact hkn
    · rw [Finset.mem_Icc]; exact hmn
    · rw [hdk, hdm]; decide
  ext ⟨a, b⟩
  rw [Finset.mem_singleton]
  constructor
  · intro hab
    unfold perm_inflection_set at hab
    rw [Finset.mem_filter, Finset.mem_product] at hab
    rcases hab with ⟨⟨ha_icc, hb_icc⟩, hab_lt, hab_prod, hab_mid⟩
    rw [Finset.mem_Icc] at ha_icc hb_icc
    have h_pos_k : ∀ x, (2 ≤ x ∧ x ≤ n - 1) →
        (0 < perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) x ↔ x = k) := by
      intro x hx
      rw [op_686_single_element_admissible_gadget_d_eq k m hk hkm x hx]
      exact op_686_single_element_admissible_gadget_d_pos k m x hk hkm hx
    have h_lt_k : ∀ x, 2 ≤ x → x < k →
        perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) x = 0 := by
      intro x h2x hxk
      have hxn : 2 ≤ x ∧ x ≤ n - 1 := by dsimp [n]; omega
      rw [op_686_single_element_admissible_gadget_d_eq k m hk hkm x hxn]
      exact op_686_single_element_admissible_gadget_d_lt_k_zero k m x ⟨h2x, hxk⟩
    have ha_eq_k : a = k := by
      by_contra ha_ne_k
      have hda_not_pos : ¬ (0 < perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) a) := by
        intro hpos
        exact ha_ne_k ((h_pos_k a ha_icc).mp hpos)
      have hdb_pos : 0 < perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) b := by
        nlinarith
      have hb_eq_k : b = k := (h_pos_k b hb_icc).mp hdb_pos
      have ha_lt_k : a < k := by omega
      have hda_zero : perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) a = 0 :=
        h_lt_k a ha_icc.1 ha_lt_k
      nlinarith
    have hb_eq_m : b = m := by
      by_contra hb_ne_m
      rcases lt_or_gt_of_ne hb_ne_m with hb_lt_m | hb_gt_m
      · have hmid : k < b ∧ b < m := ⟨by omega, hb_lt_m⟩
        have hdb_zero : perm_second_derivative (op_686_single_element_admissible_gadget_perm k m hk hkm) b = 0 := by
          rw [op_686_single_element_admissible_gadget_d_eq k m hk hkm b hb_icc]
          exact op_686_single_element_admissible_gadget_d_zero k m b hk hmid
        rw [hdb_zero, mul_zero] at hab_prod
        contradiction
      · have hm_in_mid : m ∈ Finset.Ioo a b := by
          rw [Finset.mem_Ioo]
          exact ⟨by omega, hb_gt_m⟩
        have hdm_zero := hab_mid m hm_in_mid
        rw [hdm] at hdm_zero
        contradiction
    exact Prod.ext ha_eq_k hb_eq_m
  · intro h
    cases h
    exact h_mem

/-- Every single-element inflection set is admissible (arXiv:2610.38237, Corollary 5.15). -/
theorem op_686_single_element_admissible (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    is_admissible_inflection_set {(k, m)} := by
  use 2 * m - k, op_686_single_element_admissible_gadget_perm k m hk hkm
  exact op_686_single_element_admissible_gadget_perm_inflection_set k m hk hkm
