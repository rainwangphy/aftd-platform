import AFTD.Prelude

/-!
# saturated_small_shore_two_exceptional_singletons_pool_card_eq

Topic: graphs   Node: da2206189b47

Provenance: helper lemma. OP-1957: arithmetic reduction of the saturated positive-barrier branches.

In the second small-shore arithmetic branch, the displayed total, representative, separator and size inequalities force the pool vertex count eb to equal its group count m, and the second-shore B count b1 to vanish.
-/

theorem saturated_small_shore_two_exceptional_singletons_pool_card_eq (k c m eb b0 b1 c0 d : ℕ)
    (hkc : c ≤ k) (heb : m ≤ eb)
    (htotal : b0+b1+eb+c0+d+m+6=2*k)
    (hrep : b0+b1+eb+c0+6≤c)
    (hcut : 1≤d → d+b1+eb+c≤2*k) : eb=m ∧ b1=0 := by
  have hd : 1≤d := by
    by_contra h
    omega
  have hh := hcut hd
  omega
