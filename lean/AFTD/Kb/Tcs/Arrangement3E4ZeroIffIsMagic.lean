import AFTD.Prelude
import AFTD.Kb.Tcs.IsMagicArrangement3
import AFTD.Kb.Tcs.Arrangement3E4Zero
import AFTD.Kb.Tcs.Arrangement3E4ZeroOfIsMagic
import AFTD.Kb.Tcs.Arrangement3DiophantineSystem
import AFTD.Kb.Tcs.Arrangement3SumEntries
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# arrangement3_e4_zero_iff_is_magic

Topic: combinatorics   Node: 80ae664e9a7d

Provenance: formalization of a published result. Source: arXiv:2610.38386, Proposition 5.1

An arrangement of order 3 satisfies the four-term line-sum energy zero condition $E_4(S) = 0$ if and only if it is a magic square.
-/

private lemma arrangement3_e4_zero_iff_is_magic_core
    (p00 p01 p02 p10 p11 p12 p20 p21 p22 : ℤ)
    (hsum : p00+p01+p02+p10+p11+p12+p20+p21+p22 = 0)
    (hcol : p01 + 2*p02 + p11 + 2*p12 + p21 + 2*p22 = 0)
    (hrow : p10+p11+p12+2*(p20+p21+p22) = 0)
    (hdiag : p00+p11+p22=0)
    (hanti : p02+p11+p20=0)
    (hsq : p00^2+p01^2+p02^2+p10^2+p11^2+p12^2+p20^2+p21^2+p22^2 = 60)
    (hne1 : p00 ≠ p22) (hne2 : p02 ≠ p20) (hne3 : p00 ≠ p02) (hne4 : p02 ≠ p22) :
    p00+p01+p02 = 0 ∧ p10+p11+p12=0 ∧ p20+p21+p22=0 ∧
      p00+p10+p20=0 ∧ p01+p11+p21=0 ∧ p02+p12+p22=0 := by
  set ξ := p00+p10+p20 with hξ
  set η := p00+p01+p02 with hη
  have hRel : 3*p11 = -2*(ξ+η) := by linarith
  have hdvd : 2 ∣ p11 := by omega
  obtain ⟨μ, hμ⟩ := hdvd
  have hκ : p11 = -2*(-μ) := by linarith
  set κ := -μ with hκdef
  have hξη : ξ + η = 3*κ := by linarith
  have hκA : 2*κ = p00 + p22 := by linarith
  have hκB : 2*κ = p02 + p20 := by linarith
  have h22 : p22 = -p00 - p11 := by linarith
  have h20 : p20 = -p02 - p11 := by linarith
  have h01 : p01 = η - p00 - p02 := by linarith
  have h10 : p10 = ξ - p00 - p20 := by linarith
  have h12 : p12 = ξ - p02 - p22 := by linarith
  have h21 : p21 = -2*ξ - p11 - p01 := by linarith
  have hη' : η = 3*κ - ξ := by linarith
  have heq : 4*κ^2+3*((p00-κ)^2+(p02-κ)^2)+(ξ-κ)^2+(η-κ)^2 = 30 := by
    have hident : p00^2+p01^2+p02^2+p10^2+p11^2+p12^2+p20^2+p21^2+p22^2
        = 2*(4*κ^2+3*((p00-κ)^2+(p02-κ)^2)+(ξ-κ)^2+(η-κ)^2) := by
      simp only [h22, h20, h01, h12, h21, h10, hκ, hη']; ring
    linarith [hsq, hident]
  have hc1 : p00 - κ ≠ 0 := by intro h; apply hne1; linarith
  have hc2 : p02 - κ ≠ 0 := by intro h; apply hne2; linarith
  have hc3 : (p00-κ)^2 ≠ (p02-κ)^2 := by
    intro hh
    have hprod : ((p00-κ)-(p02-κ))*((p00-κ)+(p02-κ)) = 0 := by nlinarith [hh]
    have hsub : (p00-κ)-(p02-κ) ≠ 0 := by intro h; apply hne3; linarith
    have hadd : (p00-κ)+(p02-κ) ≠ 0 := by intro h; apply hne4; linarith
    rcases mul_eq_zero.mp hprod with h | h
    · exact hsub h
    · exact hadd h
  obtain ⟨hκ0, hξ', hη'0⟩ := arrangement3_diophantine_system κ (p00-κ) (p02-κ) (ξ-κ) (η-κ)
      (by linarith) heq ⟨hc1, hc2, hc3⟩
  have hξ0 : ξ = 0 := by linarith
  have hη0 : η = 0 := by linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Proposition 5.1: an arrangement S of order 3 has E₄(S) = 0 if and only if S is a magic square. -/
theorem arrangement3_e4_zero_iff_is_magic (S : Fin 3 × Fin 3 ≃ Fin 9) :
    arrangement3_e4_zero S ↔ is_magic_arrangement3 S := by
  constructor
  · intro h
    obtain ⟨hcol, hrow, hdiag, hanti⟩ := h
    let Z : Fin 3 × Fin 3 → ℤ := fun p => ((S p).val : ℤ) + 1 - 5
    have hZcol : ∑ i : Fin 3, ∑ j : Fin 3, (j : ℤ) * Z (i,j) = 0 := by
      have key : (∑ i : Fin 3, ∑ j : Fin 3, (j : ℤ) * Z (i,j))
          = (∑ i : Fin 3, ∑ j : Fin 3, (j : ℤ) * (((S (i,j)).val : ℤ) + 1)) - 45 := by
        simp only [Z, Fin.sum_univ_three]; norm_num; ring
      rw [key, hcol]; ring
    have hZrow : ∑ i : Fin 3, ∑ j : Fin 3, (i : ℤ) * Z (i,j) = 0 := by
      have key : (∑ i : Fin 3, ∑ j : Fin 3, (i : ℤ) * Z (i,j))
          = (∑ i : Fin 3, ∑ j : Fin 3, (i : ℤ) * (((S (i,j)).val : ℤ) + 1)) - 45 := by
        simp only [Z, Fin.sum_univ_three]; norm_num; ring
      rw [key, hrow]; ring
    have hZdiag : ∑ i : Fin 3, Z (i,i) = 0 := by
      have key : (∑ i : Fin 3, Z (i,i)) = (∑ i : Fin 3, (((S (i,i)).val : ℤ) + 1)) - 15 := by
        simp only [Z, Fin.sum_univ_three]; ring
      rw [key, hdiag]; ring
    have hZanti : ∑ i : Fin 3, Z (i,i.rev) = 0 := by
      have key : (∑ i : Fin 3, Z (i,i.rev)) = (∑ i : Fin 3, (((S (i,i.rev)).val : ℤ) + 1)) - 15 := by
        simp only [Z, Fin.sum_univ_three]; ring
      rw [key, hanti]; ring
    have hZsum : ∑ i : Fin 3, ∑ j : Fin 3, Z (i,j) = 0 := by
      have key : (∑ i : Fin 3, ∑ j : Fin 3, Z (i,j))
          = (∑ i : Fin 3, ∑ j : Fin 3, (((S (i,j)).val : ℤ) + 1)) - 45 := by
        simp only [Z, Fin.sum_univ_three]; ring
      rw [key, arrangement3_sum_entries S]; ring
    have hZsq : ∑ i : Fin 3, ∑ j : Fin 3, Z (i,j)^2 = 60 := by
      have key : (∑ i : Fin 3, ∑ j : Fin 3, Z (i,j)^2)
          = (∑ i : Fin 3, ∑ j : Fin 3, ((((S (i,j)).val : ℤ) + 1)^2)) - 10 * (∑ i : Fin 3, ∑ j : Fin 3, (((S (i,j)).val : ℤ) + 1)) + 225 := by
        simp only [Z, Fin.sum_univ_three]; ring
      rw [key]
      have hsq : (∑ i : Fin 3, ∑ j : Fin 3, ((((S (i,j)).val : ℤ) + 1) ^ 2)) = 285 := by
        rw [← Fintype.sum_prod_type (fun p : Fin 3 × Fin 3 => ((((S p).val : ℤ) + 1)^2))]
        rw [Equiv.sum_comp S (fun k : Fin 9 => (((k : ℤ) + 1)^2))]
        decide
      rw [hsq, arrangement3_sum_entries S]; ring
    have hsumZ' : Z (0,0)+Z (0,1)+Z (0,2)+Z (1,0)+Z (1,1)+Z (1,2)+Z (2,0)+Z (2,1)+Z (2,2) = 0 := by
      have hh := hZsum; simp only [Fin.sum_univ_three] at hh; linarith
    have hcolZ' : Z (0,1) + 2*Z (0,2) + Z (1,1) + 2*Z (1,2) + Z (2,1) + 2*Z (2,2) = 0 := by
      have hh := hZcol; simp only [Fin.sum_univ_three] at hh; norm_num at hh; linarith
    have hrowZ' : Z (1,0)+Z (1,1)+Z (1,2) + 2*(Z (2,0)+Z (2,1)+Z (2,2)) = 0 := by
      have hh := hZrow; simp only [Fin.sum_univ_three] at hh; norm_num at hh; linarith
    have hdiagZ' : Z (0,0)+Z (1,1)+Z (2,2) = 0 := by
      have hh := hZdiag; simp only [Fin.sum_univ_three] at hh; linarith
    have hantiZ' : Z (0,2)+Z (1,1)+Z (2,0) = 0 := by
      have hh := hZanti; simp only [Fin.sum_univ_three] at hh
      rw [show (Fin.rev (0:Fin 3)) = (2:Fin 3) from by decide,
          show (Fin.rev (1:Fin 3)) = (1:Fin 3) from by decide,
          show (Fin.rev (2:Fin 3)) = (0:Fin 3) from by decide] at hh
      linarith
    have hsqZ' : Z (0,0)^2+Z (0,1)^2+Z (0,2)^2+Z (1,0)^2+Z (1,1)^2+Z (1,2)^2+Z (2,0)^2+Z (2,1)^2+Z (2,2)^2 = 60 := by
      have hh := hZsq; simp only [Fin.sum_univ_three] at hh; linarith
    have hZinj : Function.Injective Z := by
      intro p q hpq
      simp only [Z] at hpq
      have hval : (S p).val = (S q).val := by omega
      have : S p = S q := Fin.ext hval
      exact S.injective this
    have hne1 : Z (0,0) ≠ Z (2,2) := by
      intro hh; have := hZinj hh; simp at this
    have hne2 : Z (0,2) ≠ Z (2,0) := by
      intro hh; have := hZinj hh; simp at this
    have hne3 : Z (0,0) ≠ Z (0,2) := by
      intro hh; have := hZinj hh; simp at this
    have hne4 : Z (0,2) ≠ Z (2,2) := by
      intro hh; have := hZinj hh; simp at this
    obtain ⟨hR0, hR1, hR2, hD0, hD1, hD2⟩ :=
      arrangement3_e4_zero_iff_is_magic_core (Z (0,0)) (Z (0,1)) (Z (0,2)) (Z (1,0)) (Z (1,1)) (Z (1,2)) (Z (2,0)) (Z (2,1)) (Z (2,2))
        hsumZ' hcolZ' hrowZ' hdiagZ' hantiZ' hsqZ' hne1 hne2 hne3 hne4
    rw [is_magic_arrangement3]
    refine ⟨?_, ?_, hdiag, hanti⟩
    · intro i
      fin_cases i
      · beta_reduce
        change (∑ j : Fin 3, (((S (0,j)).val : ℤ) + 1)) = 15
        simp only [Fin.sum_univ_three]; simp only [Z] at hR0; linarith
      · beta_reduce
        change (∑ j : Fin 3, (((S (1,j)).val : ℤ) + 1)) = 15
        simp only [Fin.sum_univ_three]; simp only [Z] at hR1; linarith
      · beta_reduce
        change (∑ j : Fin 3, (((S (2,j)).val : ℤ) + 1)) = 15
        simp only [Fin.sum_univ_three]; simp only [Z] at hR2; linarith
    · intro j
      fin_cases j
      · beta_reduce
        change (∑ i : Fin 3, (((S (i,0)).val : ℤ) + 1)) = 15
        simp only [Fin.sum_univ_three]; simp only [Z] at hD0; linarith
      · beta_reduce
        change (∑ i : Fin 3, (((S (i,1)).val : ℤ) + 1)) = 15
        simp only [Fin.sum_univ_three]; simp only [Z] at hD1; linarith
      · beta_reduce
        change (∑ i : Fin 3, (((S (i,2)).val : ℤ) + 1)) = 15
        simp only [Fin.sum_univ_three]; simp only [Z] at hD2; linarith
  · exact arrangement3_e4_zero_of_is_magic S
