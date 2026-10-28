import AFTD.Prelude

/-!
# nat_scaled_floor_strict

Topic: combinatorics   Node: fa42732a5d79

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

For positive natural n and natural N at least n, the map i to floor(i*N/n) is strictly increasing on the natural numbers.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem nat_scaled_floor_strict
    (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) (i j : ℕ) (hij : i < j) :
    i*N/n < j*N/n := by
  have hle : i*N/n ≤ j*N/n := Nat.div_le_div_right (Nat.mul_le_mul_right N hij.le)
  by_contra hnlt
  have heq : i*N/n = j*N/n := by omega
  have hi := Nat.div_add_mod' (i*N) n
  have hj := Nat.div_add_mod' (j*N) n
  have hri := Nat.mod_lt (i*N) hn
  have hrj := Nat.mod_lt (j*N) hn
  have hprod := Nat.mul_le_mul_right N (show i+1 ≤ j by omega)
  rw [heq] at hi
  simp only [Nat.add_mul, Nat.one_mul] at hprod
  omega
