import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAnchorFamilyPerturbedValues
import AFTD.Kb.GameTheoryEconomics.EfxAnchorFamilyValues

/-!
# efx_anchor_family_perturbed_nondegenerate

Topic: fair_division   Node: 13c3032bafa8

Provenance: helper lemma. Nondegenerate arbitrary-size OP-7 Pareto obstruction, binary perturbation and experiment 11514.

If each exponent row is injective and bounded by the number of goods, every agent assigns distinct values to distinct subsets after the binary perturbation.
-/

theorem efx_anchor_family_perturbed_nondegenerate (r s : ℕ)
  (p : Fin 4 → Fin ((7+(r+r+r))+s) → ℕ)
  (hinj : ∀ i, Function.Injective (p i))
  (hbound : ∀ i g, p i g < (7+(r+r+r))+s)
  (i : Fin 4) (S T : Finset (Fin ((7+(r+r+r))+s)))
  (h : (∑ g ∈ S, efx_anchor_family_perturbed_values r s p i g) =
       (∑ g ∈ T, efx_anchor_family_perturbed_values r s p i g)) : S = T := by
  classical
  -- Decompose each perturbed sum into a large multiple of 2^M plus the binary perturbation.
  have hsum : ∀ U : Finset (Fin ((7+(r+r+r))+s)),
      (∑ g ∈ U, efx_anchor_family_perturbed_values r s p i g)
        = 2^(7+(r+r+r)+s) * (∑ g ∈ U, efx_anchor_family_values r s i g)
          + ∑ g ∈ U, 2 ^ (p i g) := by
    intro U
    simp only [efx_anchor_family_perturbed_values]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  -- The binary perturbation of any set of goods is strictly smaller than 2^M.
  have hbnd : ∀ U : Finset (Fin ((7+(r+r+r))+s)),
      (∑ g ∈ U, 2 ^ (p i g)) < 2^(7+(r+r+r)+s) := by
    intro U
    have himg : (∑ g ∈ U, 2 ^ (p i g)) = ∑ e ∈ U.image (fun g => p i g), 2^e :=
      (Finset.sum_image (f := fun e => (2:ℕ)^e) (g := fun g => p i g)
        (fun x _ y _ hxy => hinj i hxy)).symm
    rw [himg]
    exact Nat.geomSum_lt (m := 2) (n := 7+(r+r+r)+s) (by norm_num) (fun k hk => by
      simp only [Finset.mem_image] at hk
      obtain ⟨g, _, rfl⟩ := hk
      exact hbound i g)
  -- Reduce the equality modulo 2^M to get equality of the binary parts.
  have hBT : (∑ g ∈ S, 2 ^ (p i g)) = (∑ g ∈ T, 2 ^ (p i g)) := by
    have hmain : 2^(7+(r+r+r)+s) * (∑ g ∈ S, efx_anchor_family_values r s i g)
          + (∑ g ∈ S, 2 ^ (p i g))
        = 2^(7+(r+r+r)+s) * (∑ g ∈ T, efx_anchor_family_values r s i g)
          + (∑ g ∈ T, 2 ^ (p i g)) := by
      rw [← hsum S, ← hsum T]
      exact h
    have hmod := congrArg (fun x => x % 2^(7+(r+r+r)+s)) hmain
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (hbnd S),
      Nat.mod_eq_of_lt (hbnd T)] at hmod
    exact hmod
  have himgS : (∑ g ∈ S, 2 ^ (p i g)) = ∑ e ∈ S.image (fun g => p i g), 2^e :=
    (Finset.sum_image (f := fun e => (2:ℕ)^e) (g := fun g => p i g)
      (fun x _ y _ hxy => hinj i hxy)).symm
  have himgT : (∑ g ∈ T, 2 ^ (p i g)) = ∑ e ∈ T.image (fun g => p i g), 2^e :=
    (Finset.sum_image (f := fun e => (2:ℕ)^e) (g := fun g => p i g)
      (fun x _ y _ hxy => hinj i hxy)).symm
  -- Distinct powers of two with distinct exponents have distinct sums.
  have hsumimg : (∑ e ∈ S.image (fun g => p i g), 2^e)
      = (∑ e ∈ T.image (fun g => p i g), 2^e) := by
    rw [← himgS, ← himgT]
    exact hBT
  exact Finset.image_injective (hinj i)
    (Finset.geomSum_injective (n := 2) (by norm_num) hsumimg)
