import AFTD.Prelude
import AFTD.Kb.Tcs.SignedRelationStepBasisTriangular
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.SignedRelation
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TriangularNumber
import AFTD.Kb.Tcs.DualCertP

/-!
# signed_relation_step_basis_dual_solution

Topic: combinatorics   Node: 2141bcfb38c6

Provenance: helper lemma. step towards dual_certificate_identity

Forward substitution on the unit triangular system from signed_relation_step_basis_triangular constructs an integer vector y with 1 <= y j for all j such that the linear combination evaluates to 1 on every step basis vector.
-/

namespace DCB3

noncomputable def cs (n i t : ℕ) : ℝ := if 0 < t ∧ t ≤ n then (if i ≤ t - 1 then 1 else 0) else 0

theorem cs_nonneg (n i t : ℕ) : 0 ≤ cs n i t := by
  unfold cs; split_ifs <;> norm_num

theorem cs_mono {n i a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n) : cs n i a ≤ cs n i b := by
  unfold cs; split_ifs <;> first | (exfalso; omega) | norm_num

theorem sr_step (n J i : ℕ) :
    signed_relation n J (fun k : Fin n => if i ≤ k.val then 1 else 0) =
      (∑ t ∈ Finset.range (dual_cert_p (n - J + 1)), cs n i (J + t)) - cs n i (J - 1)
        - ∑ k ∈ Finset.range (dual_cert_p (n - J + 1) - 1), cs n i (n - triangular_number k) := by
  unfold signed_relation cs
  rfl

def csz (n i t : ℕ) : ℤ := if 0 < t ∧ t ≤ n then (if i ≤ t - 1 then 1 else 0) else 0

theorem cs_eq (n i t : ℕ) : cs n i t = (csz n i t : ℝ) := by
  unfold cs csz; split_ifs <;> simp

def Ez (n j i : ℕ) : ℤ :=
  (∑ t ∈ Finset.range (dual_cert_p (n - j)), csz n i (j + 1 + t)) - csz n i j
    - ∑ k ∈ Finset.range (dual_cert_p (n - j) - 1), csz n i (n - triangular_number k)

theorem sr_step_eq (n : ℕ) (j i : Fin n) :
    signed_relation n (j.val + 1) (fun k : Fin n => if i.val ≤ k.val then 1 else 0) = (Ez n j.val i.val : ℝ) := by
  have hm : n - (j.val + 1) + 1 = n - j.val := by have := j.isLt; omega
  rw [sr_step, hm, Nat.add_sub_cancel]
  simp only [cs_eq, Ez]
  push_cast
  ring

def Yf (n : ℕ) : ℕ → ℤ
  | i => 1 - ∑ j : Fin i, Yf n j.val * Ez n j.val i
decreasing_by exact j.isLt

theorem Yf_eq (n i : ℕ) : Yf n i = 1 - ∑ j ∈ Finset.range i, Yf n j * Ez n j i := by
  rw [Yf, Fin.sum_univ_eq_sum_range (fun j => Yf n j * Ez n j i)]

theorem Ez_tri (n : ℕ) (hn : 1 ≤ n) (j i : ℕ) (hj : j < n) (hi : i < n) :
    (i < j → Ez n j i = 0) ∧ (i = j → Ez n j i = 1) ∧ (j < i → Ez n j i ≤ 0) := by
  have T := signed_relation_step_basis_triangular n hn ⟨j, hj⟩ ⟨i, hi⟩
  dsimp only at T
  have e : signed_relation n (j + 1) (fun k : Fin n => if i ≤ k.val then (1 : ℝ) else 0) = (Ez n j i : ℝ) :=
    sr_step_eq n ⟨j, hj⟩ ⟨i, hi⟩
  rw [e] at T
  obtain ⟨h1, h2, h3⟩ := T
  exact ⟨fun h => by exact_mod_cast h1 h, fun h => by exact_mod_cast h2 h,
    fun h => by exact_mod_cast h3 h⟩

theorem Yf_pos (n : ℕ) (hn : 1 ≤ n) : ∀ i, i < n → 1 ≤ Yf n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [Yf_eq]
    have : ∑ j ∈ Finset.range i, Yf n j * Ez n j i ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      rw [Finset.mem_range] at hj
      have h1 := ih j hj (by omega)
      have h2 := (Ez_tri n hn j i (by omega) hi).2.2 hj
      nlinarith
    linarith

theorem dual_solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : Fin n → ℤ, (∀ j : Fin n, 1 ≤ y j) ∧
      ∀ i : Fin n, (∑ j : Fin n, (y j : ℝ) * signed_relation n (j.val + 1) (fun k => if i.val ≤ k.val then 1 else 0)) = 1 := by
  refine ⟨fun j => Yf n j.val, fun j => Yf_pos n hn j.val j.isLt, fun i => ?_⟩
  simp only [sr_step_eq]
  have key : ∑ j : Fin n, Yf n j.val * Ez n j.val i.val = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Yf n j * Ez n j i.val)]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (show i.val + 1 ≤ n by have := i.isLt; omega))]
    · rw [Finset.sum_range_succ, (Ez_tri n hn i.val i.val i.isLt i.isLt).2.1 rfl, Yf_eq n i.val]
      ring
    · intro j hj hj'
      simp only [Finset.mem_range] at hj hj'
      rw [(Ez_tri n hn j i.val hj i.isLt).1 (by omega), mul_zero]
  exact_mod_cast key

end DCB3

/-- Forward substitution on the unit triangular system from signed_relation_step_basis_triangular constructs an integer vector y with y_j >= 1 satisfying the condition on all step basis vectors. -/
theorem signed_relation_step_basis_dual_solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : Fin n → ℤ, (∀ j : Fin n, 1 ≤ y j) ∧
      ∀ i : Fin n, (∑ j : Fin n, (y j : ℝ) * signed_relation n (j.val + 1) (fun k => if i.val ≤ k.val then 1 else 0)) = 1 := by
  exact DCB3.dual_solution n hn
