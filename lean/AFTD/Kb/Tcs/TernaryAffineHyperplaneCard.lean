import AFTD.Prelude
import AFTD.Kb.Tcs.TernaryAffineHyperplane

/-!
# ternary_affine_hyperplane_card

Topic: combinatorics   Node: cbc0bc8baef8

Provenance: helper lemma. arXiv:2610.32789, Section 3.1

For every natural number $n \ge 1$, every vector $a \in (\mathbb{Z}/3\mathbb{Z})^n$ with all non-zero coordinates, and every $b \in \mathbb{Z}/3\mathbb{Z}$, the ternary affine hyperplane $\{x \in (\mathbb{Z}/3\mathbb{Z})^n \mid \sum_{i} a_i x_i = b\}$ has cardinality $3^{n - 1}$.
-/

lemma ternary_affine_hyperplane_card_succ (m : ℕ) (a : Fin (m + 1) → ZMod 3) (ha0 : a 0 ≠ 0) (b : ZMod 3) :
    (ternary_affine_hyperplane (m + 1) a b).card = 3 ^ m := by
  have hc : (Finset.univ : Finset (Fin m → ZMod 3)).card = 3 ^ m := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [← hc]
  apply Finset.card_bij (fun x _ => fun i : Fin m => x i.succ)
  · intro x hx
    exact Finset.mem_univ _
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [ternary_affine_hyperplane, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    have heq_succ : ∀ i : Fin m, x₁ i.succ = x₂ i.succ := funext_iff.mp heq
    rw [Fin.sum_univ_succ] at hx₁ hx₂
    have hsum : (∑ i : Fin m, a i.succ * x₁ i.succ) = (∑ i : Fin m, a i.succ * x₂ i.succ) := by
      congr 1
      ext i
      rw [heq_succ i]
    rw [hsum] at hx₁
    have ha0x : a 0 * x₁ 0 = a 0 * x₂ 0 := by
      linear_combination hx₁ - hx₂
    have hx0 : x₁ 0 = x₂ 0 := mul_left_cancel₀ ha0 ha0x
    ext i
    refine Fin.cases ?_ ?_ i
    · exact hx0
    · intro j
      exact heq_succ j
  · intro y _
    refine ⟨Fin.cons ((a 0)⁻¹ * (b - ∑ i : Fin m, a i.succ * y i)) y, ?_, rfl⟩
    simp only [ternary_affine_hyperplane, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.sum_univ_succ]
    change a 0 * ((a 0)⁻¹ * (b - ∑ i : Fin m, a i.succ * y i)) + (∑ i : Fin m, a i.succ * y i) = b
    rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    ring

/-- Every affine hyperplane with nonzero normal coefficients has size 3^(n-1). -/
theorem ternary_affine_hyperplane_card (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ZMod 3) (ha : ∀ i, a i ≠ 0) (b : ZMod 3) : (ternary_affine_hyperplane n a b).card = 3 ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    exact ternary_affine_hyperplane_card_succ m a (ha 0) b
