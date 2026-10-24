import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape

/-!
# mem_latin_double_three_tail_shape

Topic: combinatorics   Node: c7a37522ec95

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

A cell (i,j) belongs to the double-3-tail shape exactly when i < k-1 and j < max(3,k-i).
-/

theorem mem_latin_double_three_tail_shape (k i j : ℕ) :
    (i,j) ∈ latin_double_three_tail_shape k ↔ i < k - 1 ∧ j < max 3 (k - i) := by
  change ((i,j) ∈ ((Finset.range (k - 1)) ×ˢ Finset.range (max k 3)).filter
    (fun c => c.2 < max 3 (k - c.1))) ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega
