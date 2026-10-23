import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFTheta
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_markov_sub_eq_sum_theta

Topic: information   Node: b6b5b75138b1

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Theorem 1, eq. (13)

For a full-support Markov chain Y → X → Z, Ĩ_f(X;YZ) - Ĩ_f(X;Z) = Σ_z p_Z(z) Θ_{p_X,p_{Y|X}}(p_{X|Z=z}) (eq. (13) of arXiv:2610.21231).
-/

theorem mutual_f_information_markov_sub_eq_sum_theta {X Y Z : Type*} [Fintype X] [Fintype Y]
    [Fintype Z] (f : ℝ → ℝ) (pX : X → ℝ) (PY : X → Y → ℝ) (PZ : X → Z → ℝ)
    (hpX : ∀ x, 0 < pX x) (hsX : ∑ x, pX x = 1)
    (hPY : ∀ x y, 0 < PY x y) (hsY : ∀ x, ∑ y, PY x y = 1)
    (hPZ : ∀ x z, 0 < PZ x z) (hsZ : ∀ x, ∑ z, PZ x z = 1) :
    mutual_f_information f (fun x (yz : Y × Z) => pX x * PY x yz.1 * PZ x yz.2) -
        mutual_f_information f (fun x z => pX x * PZ x z) =
      ∑ z, (∑ x, pX x * PZ x z) *
        mutual_f_theta f pX PY (fun x => pX x * PZ x z / ∑ x', pX x' * PZ x' z) := by
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsX
  unfold mutual_f_information mutual_f_theta
  have rowYZ : ∀ x, ∑ yz : Y × Z, pX x * PY x yz.1 * PZ x yz.2 = pX x := by
    intro x
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hsZ, mul_one, hsY]
  have rowZ : ∀ x, ∑ z, pX x * PZ x z = pX x := by
    intro x; rw [← Finset.mul_sum, hsZ, mul_one]
  simp only [rowYZ, rowZ]
  set pZ : Z → ℝ := fun z => ∑ x, pX x * PZ x z with hpZ
  set q : Y → Z → ℝ := fun y z => ∑ x, pX x * PY x y * PZ x z with hq
  have hpZpos : ∀ z, 0 < pZ z := fun z =>
    Finset.sum_pos (fun x _ => mul_pos (hpX x) (hPZ x z)) ⟨Classical.arbitrary X, Finset.mem_univ _⟩
  have hqpos : ∀ y z, 0 < q y z := fun y z =>
    Finset.sum_pos (fun x _ => mul_pos (mul_pos (hpX x) (hPY x y)) (hPZ x z))
      ⟨Classical.arbitrary X, Finset.mem_univ _⟩
  have hA : ∀ y z, ∑ x, pX x * PZ x z / pZ z * PY x y = q y z / pZ z := by
    intro y z
    simp only [hq, Finset.sum_div]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  change ∑ x : X, ∑ yz : Y × Z, pX x * q yz.1 yz.2 *
        f (pX x * PY x yz.1 * PZ x yz.2 / (pX x * q yz.1 yz.2)) -
      ∑ x : X, ∑ z : Z, pX x * pZ z * f (pX x * PZ x z / (pX x * pZ z)) =
    ∑ z : Z, pZ z * (∑ y : Y, (∑ x : X, pX x * PZ x z / pZ z * PY x y) *
        ∑ x : X, pX x * f (pX x * PZ x z / pZ z * PY x y /
          (∑ x' : X, pX x' * PZ x' z / pZ z * PY x' y) / pX x) -
      ∑ x : X, pX x * f (pX x * PZ x z / pZ z / pX x))
  simp only [hA, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp only [Fintype.sum_prod_type]
    have hT : ∀ x y z, pZ z * (q y z / pZ z * (pX x * f (pX x * PZ x z / pZ z * PY x y /
        (q y z / pZ z) / pX x))) = pX x * q y z * f (pX x * PY x y * PZ x z / (pX x * q y z)) := by
      intro x y z
      have h1 := (hpZpos z).ne'
      have h2 := (hqpos y z).ne'
      have h3 := (hpX x).ne'
      have harg : pX x * PZ x z / pZ z * PY x y / (q y z / pZ z) / pX x =
          pX x * PY x y * PZ x z / (pX x * q y z) := by
        field_simp
      rw [harg]
      field_simp
    simp only [Finset.mul_sum, hT]
    exact Finset.sum_comm.trans ((Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans
      Finset.sum_comm)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hd : pX x * PZ x z / pZ z / pX x = pX x * PZ x z / (pX x * pZ z) := by
      rw [div_div, mul_comm (pZ z)]
    rw [hd]; ring
