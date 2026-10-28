import AFTD.Prelude

/-!
# cycle_power_dyadic_domain_wall

Topic: combinatorics   Node: ce3eae962c2b

Provenance: helper lemma. OP-205 / RT-1 structural-hypothesis audit following arXiv:2610.15635. A compact five-exception version of the previously computed nonperiodic domain wall6554 was independently audited in experiment7315. This formal countermodel addresses a stronger auxiliary statement without counts or periodicity; it is not a graph cover, a periodic model, an OP-205 refutation, or a research advance.

An explicit radius-eight Boolean rooted-profile system on the integers: a two-periodic left tail and a four-periodic right tail, with exceptional bit masks at roots-3,-1,0,1,3. It is used to audit which structural hypotheses are necessary.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def cycle_power_dyadic_domain_wall (p : ℤ) (a : ℕ) : Bool := (if p = -3 then 247 else
    if p = -1 then 195 else
    if p = 0 then 153 else
    if p = 1 then 243 else
    if p = 3 then 239 else
    if p < 0 then (if p % 2 = 0 then 129 else 243) else
    if p % 4 = 1 then 195 else
    if p % 4 = 3 then 255 else 129 : ℕ).testBit a
