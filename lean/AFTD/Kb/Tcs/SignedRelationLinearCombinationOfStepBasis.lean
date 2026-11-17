import AFTD.Prelude
import AFTD.Kb.Tcs.SignedRelation
import AFTD.Kb.Tcs.TriangularNumber
import AFTD.Kb.Tcs.DualCertP
import AFTD.Kb.Tcs.F

/-!
# signed_relation_linear_combination_of_step_basis

Topic: combinatorics   Node: d8399010b2b6

Provenance: helper lemma. step towards dual_certificate_identity

Because any vector x decomposes into a telescoping sum of step basis vectors with sum of differences equal to x(n-1), any linear combination of signed relations that evaluates to 1 on all step basis vectors evaluates to x(n-1) on all vectors x.
-/

namespace DCB4

noncomputable def X {n : ℕ} (x : Fin n → ℝ) (t : ℕ) : ℝ :=
  if h : 0 < t ∧ t ≤ n then x ⟨t - 1, by omega⟩ else 0

theorem sr_X (n J : ℕ) (x : Fin n → ℝ) : signed_relation n J x =
    (∑ t ∈ Finset.range (dual_cert_p (n - J + 1)), X x (J + t)) - X x (J - 1)
      - ∑ k ∈ Finset.range (dual_cert_p (n - J + 1) - 1), X x (n - triangular_number k) := rfl

theorem X_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) (t : ℕ) :
    X (∑ i ∈ s, f i) t = ∑ i ∈ s, X (f i) t := by
  unfold X; split_ifs
  · simp [Finset.sum_apply]
  · simp

theorem X_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) (t : ℕ) : X (c • x) t = c * X x t := by
  unfold X; split_ifs
  · simp
  · simp

theorem sr_sum (n J : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f : ι → Fin n → ℝ) :
    signed_relation n J (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * signed_relation n J (f i) := by
  simp only [sr_X, X_sum, X_smul, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := Finset.range (dual_cert_p (n - J + 1))),
    Finset.sum_comm (s := Finset.range (dual_cert_p (n - J + 1) - 1))]

theorem lin_comb (n : ℕ) (hn : 1 ≤ n) (y : Fin n → ℝ) :
    (∀ i : Fin n, (∑ j : Fin n, y j * signed_relation n (j.val + 1) (fun k => if i.val ≤ k.val then 1 else 0)) = 1) →
      ∀ x : Fin n → ℝ, (∑ j : Fin n, y j * signed_relation n (j.val + 1) x) = x ⟨n - 1, by omega⟩ := by
  intro hy x
  let Xn : ℕ → ℝ := fun t => if h : t < n then x ⟨t, h⟩ else 0
  let F : ℕ → ℝ := fun t => if t = 0 then 0 else Xn (t - 1)
  let d : ℕ → ℝ := fun i => F (i + 1) - F i
  have hx : x = ∑ i : Fin n, d i.val • (fun k : Fin n => if i.val ≤ k.val then (1 : ℝ) else 0) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ k.val then d i else 0), Finset.sum_ite,
      Finset.sum_const_zero, add_zero]
    have hfilt : (Finset.range n).filter (fun i => i ≤ k.val) = Finset.range (k.val + 1) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; have := k.isLt; omega
    rw [hfilt, Finset.sum_range_sub (fun i => F i)]
    simp [F, Xn, k.isLt]
  conv_lhs => rw [hx]
  simp only [sr_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ i : Fin n, ∑ j : Fin n, y j * (d i.val * signed_relation n (j.val + 1)
      (fun k : Fin n => if i.val ≤ k.val then (1 : ℝ) else 0)) = d i.val := by
    intro i
    have h1 := hy i
    calc _ = d i.val * ∑ j : Fin n, y j * signed_relation n (j.val + 1)
          (fun k : Fin n => if i.val ≤ k.val then (1 : ℝ) else 0) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = d i.val := by rw [h1, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => d i), Finset.sum_range_sub (fun i => F i)]
  simp only [F, Xn]
  have : n ≠ 0 := by omega
  simp [this, show n - 1 < n by omega]

end DCB4

/-- Any linear combination of signed relations evaluating to 1 on all step basis vectors evaluates to x(n-1) on all vectors x. -/
theorem signed_relation_linear_combination_of_step_basis (n : ℕ) (hn : 1 ≤ n) (y : Fin n → ℝ) :
    (∀ i : Fin n, (∑ j : Fin n, y j * signed_relation n (j.val + 1) (fun k => if i.val ≤ k.val then 1 else 0)) = 1) →
      ∀ x : Fin n → ℝ, (∑ j : Fin n, y j * signed_relation n (j.val + 1) x) = x ⟨n - 1, by omega⟩ := by
  exact DCB4.lin_comb n hn y
