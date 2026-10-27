import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandMiddleImpFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionPrune
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionModel
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionNoIsland
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_end_shell_fullness_of_no_island

Topic: combinatorics   Node: e3c2e3224161

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

Conversely, no-island shape in a tight exact full-coverage dyadic model forces both complete dyadic end blocks whenever either next-shell offset is selected. Together with the converse theorem this is a flat structural characterization.
-/

open Finset

theorem cycle_power_dyadic_end_shell_fullness_of_no_island
    (M : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (M+1) (x p) =
      (range (2^(M+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < M+1, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(M+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(M+1) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(M+1)-d ∧ x (v-(c : ℤ)) c = true ∧
        x (v-(c : ℤ)) (c+d) = true)
    (hshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(M+1) →
      x p a = false → x p b = true → x p c = true) :
    ∀ r < M, ∀ (p : ℤ) (a : ℕ), 2^r ≤ a → a < 2^(r+1) →
      (x p a = true ∨ x p (2^(M+1)-1-a) = true) →
      ∀ i < 2^r, x p i = true ∧ x p (2^(M+1)-1-i) = true := by
  intro r hr p a ha0 ha1 hx
  have hp : 2^(r+2) ≤ 2^(M+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hH : 2^(r+1)=2*2^r := by rw [pow_succ]; omega
  have hD : 2^(r+2)=2*2^(r+1) := by rw [pow_succ]; omega
  let b := cycle_power_dyadic_outer_projection (M+1) (r+1) (x p)
  have htb : cycle_power_dyadic_class_weight (r+2) b =
      (range (2^(r+2))).sum (fun a => (b a).toNat) :=
    (cycle_power_dyadic_outer_projection_model M (r+1) (by omega) x htight hexact hcover).1 p
  have hsb := cycle_power_dyadic_outer_projection_no_island M (r+1) (by omega) (x p) (hshape p)
  have hbf : ∀ i < 2^(r+1), cycle_power_dyadic_b_lift r b i = true := by
    rcases hx with hx | hx
    · have hba : b a = true := by
        simpa only [b,cycle_power_dyadic_outer_projection,if_pos ha1] using hx
      exact cycle_power_dyadic_no_island_middle_imp_full_prune r b htb hsb a
        ha0 (by omega) hba
    · let j := 2^(r+2)-1-a
      have hj0 : 2^(r+1) ≤ j := by dsimp [j]; omega
      have hj1 : j < 3*2^r := by dsimp [j]; omega
      have hi : j+2^(M+1)-2^((r+1)+1)=2^(M+1)-1-a := by dsimp [j]; omega
      have hbj : b j = true := by
        simpa only [b,cycle_power_dyadic_outer_projection,if_neg (by omega : ¬j<2^(r+1)),hi] using hx
      exact cycle_power_dyadic_no_island_middle_imp_full_prune r b htb hsb j
        (by omega) hj1 hbj
  have he := cycle_power_dyadic_outer_projection_prune (M+1) r (by omega) (x p)
  have hproj : ∀ i < 2^(r+1), cycle_power_dyadic_outer_projection (M+1) r (x p) i = true := by
    intro i hi
    have hh := hbf i hi
    change cycle_power_dyadic_b_lift r (cycle_power_dyadic_outer_projection (M+1) (r+1) (x p)) i = true at hh
    rw [he] at hh
    exact hh
  intro i hi
  constructor
  · simpa only [cycle_power_dyadic_outer_projection,if_pos hi] using hproj i (by omega)
  · let j := 2^(r+1)-1-i
    have hj : j < 2^(r+1) := by dsimp [j]; omega
    have hjq : ¬j < 2^r := by dsimp [j]; omega
    have hi' : j+2^(M+1)-2^(r+1)=2^(M+1)-1-i := by dsimp [j]; omega
    simpa only [cycle_power_dyadic_outer_projection,if_neg hjq,hi'] using hproj j hj
