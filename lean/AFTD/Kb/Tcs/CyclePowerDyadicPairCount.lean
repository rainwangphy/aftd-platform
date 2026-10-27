import AFTD.Prelude

/-!
# cycle_power_dyadic_pair_count

Topic: combinatorics   Node: 0770c7a41ea9

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

The finite dyadic pair sum. For ranks j at most m, it counts selected pairs at distance 2^m minus 2^j in the dyadic arc.
-/

open Finset

def cycle_power_dyadic_pair_count (m j : ℕ) (b : ℕ → Bool) : ℕ := by
  exact (range (2 ^ j)).sum (fun a => (b a && b (a + 2 ^ m - 2 ^ j)).toNat)
