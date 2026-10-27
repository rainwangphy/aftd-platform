import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanDerivative
import AFTD.Kb.Tcs.IsBent
import AFTD.Kb.Tcs.IsBalanced
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# boolean_derivative_bent_dim_eight_is_balanced

Topic: cryptography   Node: f37ea85053b2

Provenance: formalization of a published result. Source: arXiv:2610.32239, Section 2

For every bent function g on (Fin 8 → ZMod 2) and every nonzero vector v, the directional derivative of g along v is balanced.
-/

open Finset

def boolean_derivative_bent_sign_term (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma boolean_derivative_bent_zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

lemma boolean_derivative_bent_sum_sign_term_eq_card_sub_card {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) :
    ∑ x : Fin n → ZMod 2, boolean_derivative_bent_sign_term (f x) =
      ((filter (fun x => f x = 0) univ).card : ℤ) - ((filter (fun x => f x = 1) univ).card : ℤ) := by
  have h_split : (∑ x : Fin n → ZMod 2, boolean_derivative_bent_sign_term (f x)) =
      ∑ x : Fin n → ZMod 2, ((if f x = 0 then (1 : ℤ) else 0) - (if f x = 1 then (1 : ℤ) else 0)) := by
    apply sum_congr rfl
    intro x _
    dsimp [boolean_derivative_bent_sign_term]
    rcases boolean_derivative_bent_zmod2_cases (f x) with h | h
    · rw [h]; decide
    · rw [h]; decide
  rw [h_split, sum_sub_distrib]
  simp only [sum_boole]

lemma boolean_derivative_bent_card_zero_add_card_one {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) :
    (filter (fun x => f x = 0) univ).card + (filter (fun x => f x = 1) univ).card = 2 ^ n := by
  have h_not : filter (fun x => f x = 1) univ = filter (fun x => ¬ (f x = 0)) univ := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    rcases boolean_derivative_bent_zmod2_cases (f x) with h | h
    · simp [h]
    · simp [h]
  rw [h_not, card_filter_add_card_filter_not, card_univ]
  simp

lemma boolean_derivative_bent_balanced_of_sum_sign_term_zero {n : ℕ} (hn : 0 < n) (f : (Fin n → ZMod 2) → ZMod 2)
    (h_sum : ∑ x : Fin n → ZMod 2, boolean_derivative_bent_sign_term (f x) = 0) :
    is_balanced f := by
  dsimp [is_balanced]
  have h_sub := boolean_derivative_bent_sum_sign_term_eq_card_sub_card f
  rw [h_sum] at h_sub
  have h_add := boolean_derivative_bent_card_zero_add_card_one f
  have h_add' : ((filter (fun x => f x = 0) univ).card : ℤ) + ((filter (fun x => f x = 1) univ).card : ℤ) = 2 ^ n := by
    exact_mod_cast h_add
  have h_c1 : 2 * ((filter (fun x => f x = 1) univ).card : ℤ) = 2 ^ n := by linarith
  have h_two_pow : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    have : n = (n - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
    ring
  rw [h_two_pow] at h_c1
  have h_c1_eq : ((filter (fun x => f x = 1) univ).card : ℤ) = 2 ^ (n - 1) := by linarith
  exact_mod_cast h_c1_eq

lemma boolean_derivative_bent_sign_term_add (a b : ZMod 2) :
    boolean_derivative_bent_sign_term (a + b) = boolean_derivative_bent_sign_term a * boolean_derivative_bent_sign_term b := by
  revert a b; decide

lemma boolean_derivative_bent_sign_term_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ZMod 2) :
    boolean_derivative_bent_sign_term (∑ i ∈ s, f i) = ∏ i ∈ s, boolean_derivative_bent_sign_term (f i) := by
  induction' s using Finset.induction_on with i s hi ih
  · simp [boolean_derivative_bent_sign_term]
  · rw [sum_insert hi, prod_insert hi, boolean_derivative_bent_sign_term_add, ih]

lemma boolean_derivative_bent_sum_prod_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (f : (i : ι) → κ i → ℤ) :
    (∑ x : (i : ι) → κ i, ∏ i, f i (x i)) = ∏ i, ∑ j, f i j := by
  have h := (prod_univ_sum (fun i => (univ : Finset (κ i))) f).symm
  simp only [Fintype.piFinset_univ] at h
  exact h

lemma boolean_derivative_bent_sum_sign_term_zmod2_mul (a : ZMod 2) :
    (∑ w : ZMod 2, boolean_derivative_bent_sign_term (a * w)) = if a = 0 then 2 else 0 := by
  revert a; decide

lemma boolean_derivative_bent_sum_sign_term_dot_product {n : ℕ} (u : Fin n → ZMod 2) :
    (∑ ω : Fin n → ZMod 2, boolean_derivative_bent_sign_term (∑ i : Fin n, u i * ω i)) =
      if u = 0 then (2 : ℤ) ^ n else 0 := by
  have h_prod : ∀ ω : Fin n → ZMod 2,
      boolean_derivative_bent_sign_term (∑ i : Fin n, u i * ω i) = ∏ i : Fin n, boolean_derivative_bent_sign_term (u i * ω i) := fun ω =>
    boolean_derivative_bent_sign_term_sum univ (fun i => u i * ω i)
  simp_rw [h_prod]
  have h_sp := boolean_derivative_bent_sum_prod_univ (fun i (w : ZMod 2) => boolean_derivative_bent_sign_term (u i * w))
  rw [h_sp]
  simp_rw [boolean_derivative_bent_sum_sign_term_zmod2_mul]
  split_ifs with hu
  · subst hu
    simp
  · have : ∃ i, u i ≠ 0 := by
      by_contra! h
      exact hu (funext h)
    rcases this with ⟨i, hi⟩
    apply prod_eq_zero (mem_univ i)
    rw [if_neg hi]

lemma boolean_derivative_bent_zmod2_add_add_self (x v : Fin 8 → ZMod 2) : x + (x + v) + v = 0 := by
  ext i
  dsimp
  have : (x i + (x i + v i) + v i) = (x i + x i) + (v i + v i) := by ring
  rw [this]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [h2, h2, add_zero]

lemma boolean_derivative_bent_zmod2_eq_iff_add_add_zero (x y v : Fin 8 → ZMod 2) :
    x + y + v = 0 ↔ y = x + v := by
  constructor
  · intro h
    have : y = y + (x + y + v) := by rw [h, add_zero]
    rw [this]
    ext i
    dsimp
    have : y i + (x i + y i + v i) = (y i + y i) + (x i + v i) := by ring
    rw [this]
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    rw [h2, zero_add]
  · rintro rfl
    exact boolean_derivative_bent_zmod2_add_add_self x v

lemma boolean_derivative_bent_sum_y_step (g : (Fin 8 → ZMod 2) → ZMod 2) (v x : Fin 8 → ZMod 2) :
    (∑ y, boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * (if x + y + v = 0 then (2 : ℤ) ^ 8 else 0)) =
      boolean_derivative_bent_sign_term (boolean_derivative v g x) * (2 : ℤ) ^ 8 := by
  have : (∑ y, boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * (if x + y + v = 0 then (2 : ℤ) ^ 8 else 0)) =
      ∑ y, (if y = x + v then boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g (x + v)) * (2 : ℤ) ^ 8 else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    have h_iff := boolean_derivative_bent_zmod2_eq_iff_add_add_zero x y v
    by_cases hy : y = x + v
    · have h0 : x + y + v = 0 := h_iff.mpr hy
      rw [if_pos h0, if_pos hy, hy]
    · have h0 : ¬ (x + y + v = 0) := fun h => hy (h_iff.mp h)
      rw [if_neg h0, if_neg hy, mul_zero]
  rw [this, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  dsimp [boolean_derivative]
  rw [boolean_derivative_bent_sign_term_add]

lemma boolean_derivative_bent_term_decomp (g : (Fin 8 → ZMod 2) → ZMod 2) (v x y ω : Fin 8 → ZMod 2) :
    boolean_derivative_bent_sign_term (g x + ∑ i, x i * ω i) * boolean_derivative_bent_sign_term (g y + ∑ i, y i * ω i) * boolean_derivative_bent_sign_term (∑ i, v i * ω i) =
    boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * boolean_derivative_bent_sign_term (∑ i, (x + y + v) i * ω i) := by
  repeat rw [boolean_derivative_bent_sign_term_add]
  have h_dot : (∑ i, x i * ω i) + (∑ i, y i * ω i) + (∑ i, v i * ω i) = ∑ i, (x + y + v) i * ω i := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    congr 1
    ext i
    dsimp
    ring
  have h_sign_dot : boolean_derivative_bent_sign_term (∑ i, x i * ω i) * boolean_derivative_bent_sign_term (∑ i, y i * ω i) * boolean_derivative_bent_sign_term (∑ i, v i * ω i) =
      boolean_derivative_bent_sign_term (∑ i, (x + y + v) i * ω i) := by
    rw [← boolean_derivative_bent_sign_term_add, ← boolean_derivative_bent_sign_term_add, h_dot]
  have : boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (∑ i, x i * ω i) * (boolean_derivative_bent_sign_term (g y) * boolean_derivative_bent_sign_term (∑ i, y i * ω i)) * boolean_derivative_bent_sign_term (∑ i, v i * ω i) =
      boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * (boolean_derivative_bent_sign_term (∑ i, x i * ω i) * boolean_derivative_bent_sign_term (∑ i, y i * ω i) * boolean_derivative_bent_sign_term (∑ i, v i * ω i)) := by ring
  rw [this, h_sign_dot]

lemma boolean_derivative_bent_sum_sq_mul_swap {α : Type*} [Fintype α] [DecidableEq α] (f : α → α → ℤ) (c : α → ℤ) :
    (∑ ω, (∑ x, f x ω) ^ 2 * c ω) = ∑ x, ∑ y, ∑ ω, f x ω * f y ω * c ω := by
  have h1 : (∑ ω, (∑ x, f x ω) ^ 2 * c ω) = ∑ ω, ∑ x, ∑ y, f x ω * f y ω * c ω := by
    apply sum_congr rfl
    intro ω _
    rw [sq, sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro x _
    rw [sum_mul]
  rw [h1, sum_comm]
  congr 1
  ext x
  rw [sum_comm]

/-- The directional derivative of a bent function on (Fin 8 → ZMod 2) along a nonzero vector is balanced. -/
theorem boolean_derivative_bent_dim_eight_is_balanced (g : (Fin 8 → ZMod 2) → ZMod 2) (hg : is_bent g) (v : Fin 8 → ZMod 2) (hv : v ≠ 0) : is_balanced (boolean_derivative v g) := by
  apply boolean_derivative_bent_balanced_of_sum_sign_term_zero (by decide)
  have hg_sq : ∀ ω : Fin 8 → ZMod 2,
      (∑ x : Fin 8 → ZMod 2, boolean_derivative_bent_sign_term (g x + ∑ i, x i * ω i)) ^ 2 = (2 : ℤ) ^ 8 := by
    intro ω
    have h_abs := hg ω
    have h_def : (∑ x : Fin 8 → ZMod 2, boolean_derivative_bent_sign_term (g x + ∑ i, x i * ω i)) =
        ∑ x : Fin 8 → ZMod 2, if g x + ∑ i, x i * ω i = 0 then 1 else -1 := rfl
    have : (∑ x, boolean_derivative_bent_sign_term (g x + ∑ i, x i * ω i)) ^ 2 =
        |∑ x, boolean_derivative_bent_sign_term (g x + ∑ i, x i * ω i)| ^ 2 := (sq_abs _).symm
    rw [this, h_def, h_abs]
    rfl
  let term (x ω : Fin 8 → ZMod 2) : ℤ := boolean_derivative_bent_sign_term (g x + ∑ i, x i * ω i)
  have hS_1 : (∑ ω : Fin 8 → ZMod 2, (∑ x, term x ω) ^ 2 * boolean_derivative_bent_sign_term (∑ i, v i * ω i)) = 0 := by
    have : (∑ ω : Fin 8 → ZMod 2, (∑ x, term x ω) ^ 2 * boolean_derivative_bent_sign_term (∑ i, v i * ω i)) =
        ∑ ω : Fin 8 → ZMod 2, (2 : ℤ) ^ 8 * boolean_derivative_bent_sign_term (∑ i, v i * ω i) := by
      apply sum_congr rfl
      intro ω _
      rw [hg_sq ω]
    rw [this, ← mul_sum, boolean_derivative_bent_sum_sign_term_dot_product]
    rw [if_neg hv, mul_zero]
  have hS_2 : (∑ ω : Fin 8 → ZMod 2, (∑ x, term x ω) ^ 2 * boolean_derivative_bent_sign_term (∑ i, v i * ω i)) =
      (2 : ℤ) ^ 8 * ∑ x, boolean_derivative_bent_sign_term (boolean_derivative v g x) := by
    rw [boolean_derivative_bent_sum_sq_mul_swap term (fun (ω : Fin 8 → ZMod 2) => boolean_derivative_bent_sign_term (∑ i, v i * ω i))]
    have h_inner : ∀ x y : Fin 8 → ZMod 2, (∑ ω : Fin 8 → ZMod 2, term x ω * term y ω * boolean_derivative_bent_sign_term (∑ i, v i * ω i)) =
        boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * (if x + y + v = 0 then (2 : ℤ) ^ 8 else 0) := by
      intro x y
      have h1 : (∑ ω : Fin 8 → ZMod 2, term x ω * term y ω * boolean_derivative_bent_sign_term (∑ i, v i * ω i)) =
          ∑ ω : Fin 8 → ZMod 2, boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * boolean_derivative_bent_sign_term (∑ i, (x + y + v) i * ω i) := by
        apply sum_congr rfl
        intro ω _
        exact boolean_derivative_bent_term_decomp g v x y ω
      rw [h1, ← mul_sum, boolean_derivative_bent_sum_sign_term_dot_product]
    have h_swap2 : (∑ x, ∑ y, ∑ ω : Fin 8 → ZMod 2, term x ω * term y ω * boolean_derivative_bent_sign_term (∑ i, v i * ω i)) =
        ∑ x, ∑ y, boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * (if x + y + v = 0 then (2 : ℤ) ^ 8 else 0) := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      exact h_inner x y
    rw [h_swap2]
    have h_y_all : (∑ x, ∑ y, boolean_derivative_bent_sign_term (g x) * boolean_derivative_bent_sign_term (g y) * (if x + y + v = 0 then (2 : ℤ) ^ 8 else 0)) =
        ∑ x, boolean_derivative_bent_sign_term (boolean_derivative v g x) * (2 : ℤ) ^ 8 := by
      apply sum_congr rfl
      intro x _
      exact boolean_derivative_bent_sum_y_step g v x
    rw [h_y_all, ← sum_mul]
    ring
  have h_mult : (2 : ℤ) ^ 8 * ∑ x, boolean_derivative_bent_sign_term (boolean_derivative v g x) = 0 := by
    rw [← hS_2, hS_1]
  have h256 : ((2 : ℤ) ^ 8) ≠ 0 := by decide
  exact mul_eq_zero.mp h_mult |>.resolve_left h256
