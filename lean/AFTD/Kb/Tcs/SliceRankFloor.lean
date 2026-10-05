import AFTD.Prelude

/-!
# slice_rank_floor

Topic: quantum   Node: 752a35a49b2a

The slice-rank lower bound floor G(k) for the GF(2^k) multiplication oracle is the sum over i from 0 to 3k-1 of ceil((2k+2)/2^i).
-/

/-- The Griesmer slice-rank floor G(k) for the GF(2^k) multiplication oracle. -/
def slice_rank_floor (k : ℕ) : ℕ := ∑ i ∈ Finset.range (3 * k), (2 * k + 2 + 2 ^ i - 1) / 2 ^ i
