import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# nat_scaled_floor_gap_threshold

Topic: combinatorics   Node: 33c95837928c

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

Let n,N,k,K be natural numbers with n positive, k*N at most K*n, and (K+1)*n at most (k+1)*N. For natural i at most j, j-i is at most k if and only if floor(j*N/n)-floor(i*N/n) is at most K.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem nat_scaled_floor_gap_threshold
    (n N k K : ℕ) (hn : 0 < n)
    (hlo : k*N ≤ K*n) (hhi : (K+1)*n ≤ (k+1)*N)
    (i j : ℕ) (hij : i ≤ j) :
    j-i ≤ k ↔ j*N/n-i*N/n ≤ K := by
  let A := i*N/n
  let B := j*N/n
  have hAB : A ≤ B := Nat.div_le_div_right (Nat.mul_le_mul_right N hij)
  have hA : n*A+(i*N)%n = i*N := by
    dsimp [A]
    nlinarith [Nat.div_add_mod' (i*N) n]
  have hB : n*B+(j*N)%n = j*N := by
    dsimp [B]
    nlinarith [Nat.div_add_mod' (j*N) n]
  have hri := Nat.mod_lt (i*N) hn
  have hrj := Nat.mod_lt (j*N) hn
  change j-i ≤ k ↔ B-A ≤ K
  constructor
  · intro h
    have hprod := Nat.mul_le_mul_right N (show j ≤ i+k by omega)
    by_contra hnot
    have hgap : A+K+1 ≤ B := by omega
    have hmul := Nat.mul_le_mul_left n hgap
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hprod hmul
    rw [Nat.mul_comm K n] at hlo
    omega
  · intro h
    by_contra hnot
    have hprod := Nat.mul_le_mul_right N (show i+k+1 ≤ j by omega)
    have hgap : B ≤ A+K := by omega
    have hmul := Nat.mul_le_mul_left n hgap
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hprod hmul hhi
    rw [Nat.mul_comm K n] at hhi
    omega
