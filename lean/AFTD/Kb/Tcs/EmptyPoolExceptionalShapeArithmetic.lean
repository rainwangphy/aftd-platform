import AFTD.Prelude

/-!
# empty_pool_exceptional_shape_arithmetic

Topic: graphs   Node: ad55b7698040

Provenance: helper lemma. OP-1957; empty-pool exceptional aggregate pattern, experiments 41503 and 41553.

The stated total, representative, and cut counts force the first shore to occupy the entire opposite block and the second shore to be a singleton.
-/

theorem empty_pool_exceptional_shape_arithmetic
    (k c b0 c0 d0 b1 : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (htotal : b0+c0+d0+b1+6=2*k)
    (hrep : b0+b1+c0+6 ≤ c)
    (hD : d0 ≤ 2*k-c)
    (hcut : 1 ≤ d0 → d0+b1 ≤ 2*k-c) :
    d0=2*k-c ∧ b1=0 ∧ b0+c0+6=c := by
  omega
