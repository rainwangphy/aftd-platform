import AFTD.Prelude

/-!
# dense_four_block_matching_barrier_arithmetic

Topic: graphs   Node: 3fce82e5d480

Provenance: helper lemma. OP-1957; arithmetic for the generalized deleted-four-block matching barrier, experiment 39978.

The displayed odd group sizes and separator inequalities are incompatible with both the small- and large-separator degree alternatives.
-/

set_option maxHeartbeats 2000000

theorem dense_four_block_matching_barrier_arithmetic
    (k u d s q : ℕ) (n : Fin q → ℕ)
    (hk : 7 ≤ k) (hu : u ≤ k-4) (hsmall : u+d ≤ k)
    (hslo : 2*k ≤ s+u+d+5) (hshi : s ≤ k-1)
    (hq : 2*k+s ≤ q+u+d+3)
    (hodd : ∀ i, Odd (n i))
    (htotal : (∑ i : Fin q, n i) + s+u+d+5 = 4*k)
    (hnosingle : s ≤ k-4 → ∀ i, 2 ≤ n i)
    (hBC : k-3 ≤ s → 7 ≤ ∑ i : Fin q, if 3 ≤ n i then n i else 0) : False := by
  classical
  have hn1 : ∀ i, 1 ≤ n i := by
    intro i
    obtain ⟨t,ht⟩ := hodd i
    omega
  by_cases hs : s ≤ k-4
  · have hn3 : ∀ i, 3 ≤ n i := by
      intro i
      have hh := hnosingle hs i
      obtain ⟨t,ht⟩ := hodd i
      omega
    have hb : 3*q ≤ ∑ i : Fin q, n i := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q))) (fun i _ => hn3 i)
      simpa [Nat.mul_comm] using hh
    omega
  · have hs' : k-3 ≤ s := by omega
    have hlarge := hBC hs'
    have hterm : ∀ i : Fin q, 2 * (if 3 ≤ n i then n i else 0) ≤ 3 * (n i - 1) := by
      intro i
      have hn := hn1 i
      split_ifs with h
      · omega
      · omega
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q))) (fun i _ => hterm i)
    have hsumn : (∑ i : Fin q, (n i - 1)) + q = ∑ i : Fin q, n i := by
      have hh : (∑ i : Fin q, (n i - 1 + 1)) = ∑ i : Fin q, n i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := hn1 i
        omega
      simpa [Finset.sum_add_distrib] using hh
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
    omega
