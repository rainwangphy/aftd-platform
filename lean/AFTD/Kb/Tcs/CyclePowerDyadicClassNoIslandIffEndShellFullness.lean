import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicEndShellFullnessOfNoIsland
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfEndShellFullness
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_class_no_island_iff_end_shell_fullness

Topic: combinatorics   Node: 0a267e6cb1b2

Provenance: helper lemma. Uniform structural characterization for OP-205 / RT-1 following arXiv:2610.15635 Section 3. This combines the checked direct-projection reduction and the converse middle-fullness argument; it does not settle optimal-count shape or the original graph covering number.

In any tight exact full-coverage dyadic class model, two-end-interval/no-island shape is equivalent to this explicit condition on the original profile at every scale: selecting either member of a reflected dyadic shell fills both smaller end blocks. Neither side is derived here from optimal counts.
-/

open Finset

theorem cycle_power_dyadic_class_no_island_iff_end_shell_fullness
    (M : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (M+1) (x p) =
      (range (2^(M+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < M+1, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(M+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(M+1) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(M+1)-d ∧ x (v-(c : ℤ)) c = true ∧
        x (v-(c : ℤ)) (c+d) = true)
 :
    (∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(M+1) →
      x p a = false → x p b = true → x p c = true) ↔
    (∀ r < M, ∀ (p : ℤ) (a : ℕ), 2^r ≤ a → a < 2^(r+1) →
      (x p a = true ∨ x p (2^(M+1)-1-a) = true) →
      ∀ i < 2^r, x p i = true ∧ x p (2^(M+1)-1-i) = true) := by
  constructor
  · intro hs
    exact cycle_power_dyadic_end_shell_fullness_of_no_island M x htight hexact hcover hs
  · intro hs
    exact cycle_power_dyadic_no_island_of_end_shell_fullness M x htight hexact hcover hs
