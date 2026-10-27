import AFTD.Prelude

/-!
# cycle_power_dyadic_neighbour_pair_count

Topic: combinatorics   Node: 4ed855788d27

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

The finite neighbour pair sum. For ranks j strictly below m, it counts selected pairs at distance 2^m minus 2^j minus one in the dyadic arc.
-/

open Finset

def cycle_power_dyadic_neighbour_pair_count (m j : ℕ) (b : ℕ → Bool) : ℕ := (range (2 ^ j + 1)).sum (fun a => (b a && b (a + 2 ^ m - 2 ^ j - 1)).toNat)
