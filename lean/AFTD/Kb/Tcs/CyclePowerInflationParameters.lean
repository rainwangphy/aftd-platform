import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_inflation_parameters

Topic: combinatorics   Node: d365aeab1734

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

For natural k at least one and natural n at least both 2*k+2 and 2*k squared, put q=floor((n+k)/(k+1)). Then q is at least two, n is at most q*(2*k+1), q*(2*k+1) is at most 2*n, and (2*k+1)*n is at most (k+1)*q*(2*k+1).
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_inflation_parameters
    (n k : ℕ) (hk : 1 ≤ k) (hn₀ : 2*k+2 ≤ n) (hn₂ : 2*k^2 ≤ n) :
    let q := (n+k)/(k+1)
    2 ≤ q ∧ n ≤ q*(2*k+1) ∧ q*(2*k+1) ≤ 2*n ∧
      (2*k+1)*n ≤ (k+1)*(q*(2*k+1)) := by
  let q := (n+k)/(k+1)
  have hmod := Nat.mod_lt (n+k) (by omega : 0 < k+1)
  have hdiv := Nat.div_add_mod' (n+k) (k+1)
  change q*(k+1)+(n+k)%(k+1) = n+k at hdiv
  have hqn : n ≤ q*(k+1) := by omega
  have hqupper : q*(k+1) ≤ n+k := by omega
  have hq : 2 ≤ q := by
    by_contra hn
    have hmul := Nat.mul_le_mul_right (k+1) (show q ≤ 1 by omega)
    nlinarith
  have hNn : n ≤ q*(2*k+1) := by nlinarith
  have hN2 : q*(2*k+1) ≤ 2*n := by
    by_contra hn
    have hmul := Nat.mul_le_mul_right (k+1) (show 2*n+1 ≤ q*(2*k+1) by omega)
    have hqu := Nat.mul_le_mul_right (2*k+1) hqupper
    nlinarith
  have hgap : (2*k+1)*n ≤ (k+1)*(q*(2*k+1)) := by
    have hmul := Nat.mul_le_mul_right (2*k+1) hqn
    nlinarith
  exact ⟨hq, hNn, hN2, hgap⟩
