import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairPerturbedValues

/-!
# efx_allsource_three_pair_perturbed_nondegenerate

Topic: fair_division   Node: 10c4212e91bf

Provenance: helper lemma. Binary perturbation of the four-agent three-split barrier; experiment 11706 and the integer-gap projection.

Each agent gives distinct values to distinct subsets of goods.
-/

def efx_allsource_three_pair_perturbed_nondegenerate_exp : Fin 4 → Fin 9 → ℕ :=
  ![![7, 8, 0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 7, 8, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 7, 8, 4, 5, 6],
    ![0, 1, 2, 3, 4, 5, 7, 8, 6]]

lemma efx_allsource_three_pair_perturbed_nondegenerate_exp_inj (i : Fin 4) :
    Function.Injective (efx_allsource_three_pair_perturbed_nondegenerate_exp i) := by
  intro a b h
  fin_cases i <;> fin_cases a <;> fin_cases b <;> revert h <;> decide

lemma efx_allsource_three_pair_perturbed_nondegenerate_modEq (i : Fin 4) (g : Fin 9) :
    efx_allsource_three_pair_perturbed_values i g ≡ 2 ^ efx_allsource_three_pair_perturbed_nondegenerate_exp i g [MOD 512] := by
  fin_cases i <;> fin_cases g <;> decide

lemma efx_allsource_three_pair_perturbed_nondegenerate_sum_lt (i : Fin 4) (S : Finset (Fin 9)) :
    ∑ g ∈ S, 2 ^ efx_allsource_three_pair_perturbed_nondegenerate_exp i g < 512 := by
  calc
    ∑ g ∈ S, 2 ^ efx_allsource_three_pair_perturbed_nondegenerate_exp i g
      ≤ ∑ g : Fin 9, 2 ^ efx_allsource_three_pair_perturbed_nondegenerate_exp i g :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ < 512 := by
      fin_cases i <;> decide

theorem efx_allsource_three_pair_perturbed_nondegenerate (i : Fin 4) (S T : Finset (Fin 9))
  (h : (∑ g ∈ S, efx_allsource_three_pair_perturbed_values i g) = ∑ g ∈ T, efx_allsource_three_pair_perturbed_values i g) : S = T := by
  set e := efx_allsource_three_pair_perturbed_nondegenerate_exp i
  have he_inj : Function.Injective e := efx_allsource_three_pair_perturbed_nondegenerate_exp_inj i
  have hS : (∑ g ∈ S, efx_allsource_three_pair_perturbed_values i g) ≡
            (∑ g ∈ S, 2 ^ e g) [MOD 512] :=
    Nat.ModEq.sum (fun g _ => efx_allsource_three_pair_perturbed_nondegenerate_modEq i g)
  have hT : (∑ g ∈ T, efx_allsource_three_pair_perturbed_values i g) ≡
            (∑ g ∈ T, 2 ^ e g) [MOD 512] :=
    Nat.ModEq.sum (fun g _ => efx_allsource_three_pair_perturbed_nondegenerate_modEq i g)
  have hmod : (∑ g ∈ S, 2 ^ e g) ≡ (∑ g ∈ T, 2 ^ e g) [MOD 512] :=
    hS.symm.trans (h ▸ hT)
  have ltS := efx_allsource_three_pair_perturbed_nondegenerate_sum_lt i S
  have ltT := efx_allsource_three_pair_perturbed_nondegenerate_sum_lt i T
  rw [Nat.ModEq] at hmod
  rw [Nat.mod_eq_of_lt ltS, Nat.mod_eq_of_lt ltT] at hmod
  have hgeom : (∑ k ∈ S.image e, 2 ^ k) = ∑ k ∈ T.image e, 2 ^ k := by
    rw [Finset.sum_image (fun x _ y _ h => he_inj h),
        Finset.sum_image (fun x _ y _ h => he_inj h),
        hmod]
  have himage : S.image e = T.image e :=
    Finset.geomSum_injective (by norm_num) hgeom
  exact Finset.image_injective he_inj himage
