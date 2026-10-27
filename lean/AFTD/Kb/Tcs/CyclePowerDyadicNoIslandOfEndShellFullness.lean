import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfOuterProjectionFullness

/-!
# cycle_power_dyadic_no_island_of_end_shell_fullness

Topic: combinatorics   Node: afc901210b6f

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

In a tight exact full-coverage model, class no-island shape follows from the explicit shell condition: selecting either offset a or its reflection with 2^r≤a<2^(r+1) forces both complete end blocks of width2^r, for EVERY r below the top half-radius. This does not derive shell fullness from optimal counts.
-/

open Finset

theorem cycle_power_dyadic_no_island_of_end_shell_fullness
    (M : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (M+1) (x p) =
      (range (2^(M+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < M+1, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(M+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(M+1) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(M+1)-d ∧ x (v-(c : ℤ)) c = true ∧
        x (v-(c : ℤ)) (c+d) = true)
    (hshell : ∀ r < M, ∀ (p : ℤ) (a : ℕ), 2^r ≤ a → a < 2^(r+1) →
      (x p a = true ∨ x p (2^(M+1)-1-a) = true) →
      ∀ i < 2^r, x p i = true ∧ x p (2^(M+1)-1-i) = true) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(M+1) →
      x p a = false → x p b = true → x p c = true := by
  apply cycle_power_dyadic_no_island_of_outer_projection_fullness M x htight hexact hcover
  intro r hr p a ha0 ha1 hxa
  have hp : 2^(r+2) ≤ 2^(M+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hH : 2^(r+1)=2*2^r := by rw [pow_succ]; omega
  have hD : 2^(r+2)=2*2^(r+1) := by rw [pow_succ]; omega
  have houter : ∀ i < 2^r, x p i = true ∧ x p (2^(M+1)-1-i) = true := by
    by_cases hal : a < 2^(r+1)
    · have hx : x p a = true := by
        simpa only [cycle_power_dyadic_outer_projection,if_pos hal] using hxa
      exact hshell r hr p a ha0 hal (Or.inl hx)
    · let j := 2^(r+2)-1-a
      have hj0 : 2^r ≤ j := by dsimp [j]; omega
      have hj1 : j < 2^(r+1) := by dsimp [j]; omega
      have hi : a+2^(M+1)-2^((r+1)+1)=2^(M+1)-1-j := by dsimp [j]; omega
      have hx : x p (2^(M+1)-1-j) = true := by
        simpa only [cycle_power_dyadic_outer_projection,if_neg hal,hi] using hxa
      exact hshell r hr p j hj0 hj1 (Or.inr hx)
  intro i hi
  by_cases hil : i < 2^r
  · simpa only [cycle_power_dyadic_outer_projection,if_pos hil] using (houter i hil).1
  · let j := 2^(r+1)-1-i
    have hj : j < 2^r := by dsimp [j]; omega
    have he : i+2^(M+1)-2^(r+1)=2^(M+1)-1-j := by dsimp [j]; omega
    simpa only [cycle_power_dyadic_outer_projection,if_neg hil,he] using (houter j hj).2
