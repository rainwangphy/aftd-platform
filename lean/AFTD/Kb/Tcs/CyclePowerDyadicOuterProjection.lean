import AFTD.Prelude

/-!
# cycle_power_dyadic_outer_projection

Topic: combinatorics   Node: 157a2857fecc

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

Project a radius-2^m Boolean class to its first and last 2^r offsets, compressing them to a radius-2^(r+1) profile. The intended range is r+1≤m.
-/

open Finset

def cycle_power_dyadic_outer_projection (m r : ℕ) (b : ℕ → Bool) (a : ℕ) : Bool := if a < 2^r then b a else b (a+2^m-2^(r+1))
