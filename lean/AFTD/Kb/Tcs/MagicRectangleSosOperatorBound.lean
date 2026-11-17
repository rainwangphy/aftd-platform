import AFTD.Prelude
import AFTD.Kb.Tcs.MagicRectangleSosCertificate
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul
import AFTD.Kb.Tcs.V

/-!
# magic_rectangle_sos_operator_bound

Topic: quantum   Node: d114d884b801

Provenance: helper lemma. arXiv:2610.12001, Theorem 3.1, operator inequality following the sum-of-squares identity.

For the self-adjoint involutions and commutation relations in the rectangle certificate, the associated correlation operator is bounded above by twice the square root of six times the identity.
-/

theorem in937_rectangle_sos_operator_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D C B : Fin 3 → (H →L[ℂ] H))
    (hD_sa : ∀ j, IsSelfAdjoint (D j))
    (hC_sa : ∀ j, IsSelfAdjoint (C j))
    (hB_sa : ∀ j, IsSelfAdjoint (B j))
    (hD_sq : ∀ j, D j ^ 2 = 1)
    (hC_sq : ∀ j, C j ^ 2 = 1)
    (hB_sq : ∀ j, B j ^ 2 = 1)
    (hD_prod : D 0 * D 1 * D 2 = 1)
    (hC_prod : C 0 * C 1 * C 2 = -1)
    (hD_comm : ∀ j k, D j * D k = D k * D j)
    (hC_comm : ∀ j k, C j * C k = C k * C j)
    (hDB_comm : ∀ j k, D j * B k = B k * D j)
    (hCB_comm : ∀ j k, C j * B k = B k * C j) :
    (∑ j : Fin 3, (D j + C j) * B j) ≤ (2 * Real.sqrt 6) • (1 : H →L[ℂ] H) := by
  let X := fun j => D j + C j
  let Y := fun j => D j - C j
  let Z := fun j => X j * B j
  let V := fun j => X (j + 1) * B (j + 2) + X (j + 2) * B (j + 1)
  let W := fun j => Y (j + 1) * B (j + 2) + Y (j + 2) * B (j + 1)
  let S := ∑ j : Fin 3, X j * B j
  let r : ℝ := Real.sqrt 6
  let q : ℝ := 2 * r / 3
  change S ≤ (2 * r) • (1 : H →L[ℂ] H)
  have hX (j : Fin 3) : IsSelfAdjoint (X j) := (hD_sa j).add (hC_sa j)
  have hY (j : Fin 3) : IsSelfAdjoint (Y j) := (hD_sa j).sub (hC_sa j)
  have hXB (j k : Fin 3) : Commute (X j) (B k) := by
    change (D j + C j) * B k = B k * (D j + C j)
    rw [add_mul, mul_add, hDB_comm, hCB_comm]
  have hYB (j k : Fin 3) : Commute (Y j) (B k) := by
    change (D j - C j) * B k = B k * (D j - C j)
    rw [sub_mul, mul_sub, hDB_comm, hCB_comm]
  have hZ (j : Fin 3) : IsSelfAdjoint (Z j) := ((hX j).commute_iff (hB_sa j)).mp (hXB j j)
  have hV (j : Fin 3) : IsSelfAdjoint (V j) :=
    (((hX (j + 1)).commute_iff (hB_sa (j + 2))).mp (hXB (j + 1) (j + 2))).add
      (((hX (j + 2)).commute_iff (hB_sa (j + 1))).mp (hXB (j + 2) (j + 1)))
  have hW (j : Fin 3) : IsSelfAdjoint (W j) :=
    (((hY (j + 1)).commute_iff (hB_sa (j + 2))).mp (hYB (j + 1) (j + 2))).add
      (((hY (j + 2)).commute_iff (hB_sa (j + 1))).mp (hYB (j + 2) (j + 1)))
  have hreal (t : ℝ) : IsSelfAdjoint t := IsSelfAdjoint.all t
  have h1 (j : Fin 3) : IsSelfAdjoint (Z j - q • (1 : H →L[ℂ] H)) :=
    (hZ j).sub ((hreal q).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  have h2 (j : Fin 3) : IsSelfAdjoint (Y j - (1 / r) • V j) :=
    (hY j).sub ((hreal (1 / r)).smul (hV j))
  have h3 (j : Fin 3) : IsSelfAdjoint (X j + q • B j - q • W j) :=
    ((hX j).add ((hreal q).smul (hB_sa j))).sub ((hreal q).smul (hW j))
  have hsquare (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) : 0 ≤ T ^ 2 := by
    simpa only [hT.star_eq, sq] using (star_mul_self_nonneg T)
  have hs1 : 0 ≤ ∑ j : Fin 3, (Z j - q • (1 : H →L[ℂ] H)) ^ 2 :=
    Finset.sum_nonneg fun j _ => hsquare _ (h1 j)
  have hs2 : 0 ≤ ∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2 :=
    Finset.sum_nonneg fun j _ => hsquare _ (h2 j)
  have hs3 : 0 ≤ ∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2 :=
    Finset.sum_nonneg fun j _ => hsquare _ (h3 j)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp1 : 0 ≤ 5 * r / 64 := by positivity
  have hp2 : 0 ≤ r / 12 := by positivity
  have hp3 : 0 ≤ r / 192 := by positivity
  have hcert : (2 * r) • (1 : H →L[ℂ] H) - S =
      (5 * r / 64) • (∑ j : Fin 3, (Z j - q • 1) ^ 2) +
      (r / 12) • (∑ j : Fin 3, (Y j - (1 / r) • V j) ^ 2) +
      (r / 192) • (∑ j : Fin 3, (X j + q • B j - q • W j) ^ 2) :=
    magic_rectangle_sos_certificate D C B hD_sa hC_sa hB_sa hD_sq hC_sq hB_sq
      hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm
  apply sub_nonneg.mp
  rw [hcert]
  exact add_nonneg (add_nonneg (smul_nonneg hp1 hs1) (smul_nonneg hp2 hs2)) (smul_nonneg hp3 hs3)

theorem magic_rectangle_sos_operator_bound :
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D C B : Fin 3 → (H →L[ℂ] H)),
    (∀ j, IsSelfAdjoint (D j)) → (∀ j, IsSelfAdjoint (C j)) → (∀ j, IsSelfAdjoint (B j)) →
    (∀ j, D j ^ 2 = 1) → (∀ j, C j ^ 2 = 1) → (∀ j, B j ^ 2 = 1) →
    D 0 * D 1 * D 2 = 1 → C 0 * C 1 * C 2 = -1 →
    (∀ j k, D j * D k = D k * D j) → (∀ j k, C j * C k = C k * C j) →
    (∀ j k, D j * B k = B k * D j) → (∀ j k, C j * B k = B k * C j) →
    (∑ j : Fin 3, (D j + C j) * B j) ≤ (2 * Real.sqrt 6) • (1 : H →L[ℂ] H) := by
  intro H _ _ _ D C B hD_sa hC_sa hB_sa hD_sq hC_sq hB_sq hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm
  exact in937_rectangle_sos_operator_bound D C B hD_sa hC_sa hB_sa hD_sq hC_sq hB_sq hD_prod hC_prod hD_comm hC_comm hDB_comm hCB_comm
