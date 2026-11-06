import AFTD.Prelude
import AFTD.Kb.Tcs.BhDensePrime
import AFTD.Kb.Tcs.MomentBlock

/-!
# bh_dense_stage

Topic: combinatorics   Node: b0856dcec9aa

Provenance: helper lemma. step towards infinite_bh_set_upper_density_eq_one_div_h

The `k`-th stage of the construction (paper (3.2)): `S_0 = {1}` and `S_{k+1} = S_k ∪ (M_k + B_q)`, where `q = q_k` is a prime exceeding both `h` and `h · max S_k`, `D = h^(h-1) q^h` bounds the block, and `M_k = (h-1)D + q`.
-/

/-- Stage `k` of the recursive construction: start with `{1}` and repeatedly append a translated moment-curve block. -/
noncomputable def bh_dense_stage (h : ℕ) : ℕ → Finset ℕ := fun k => Nat.rec {1} (fun _ S =>
    let n := S.sup id
    let q := bh_dense_prime h n
    let D := h ^ (h - 1) * q ^ h
    let M := (h - 1) * D + q
    S ∪ (moment_block h q).image (fun x => M + x)) k
