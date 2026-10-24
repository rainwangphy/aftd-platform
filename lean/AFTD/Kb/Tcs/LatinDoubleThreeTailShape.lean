import AFTD.Prelude

/-!
# latin_double_three_tail_shape

Topic: combinatorics   Node: 3188cfc119cd

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

For k at least 5, the Young diagram with row lengths (k,k-1,...,4,3,3). Its i-th row has length max(3,k-i) for i < k-1 and is empty thereafter.
-/

def latin_double_three_tail_shape (k : ℕ) : YoungDiagram := {
  cells := ((Finset.range (k - 1)) ×ˢ Finset.range (max k 3)).filter
    (fun c => c.2 < max 3 (k - c.1))
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb ⊢
    exact ⟨⟨lt_of_le_of_lt hab.1 hb.1.1, lt_of_le_of_lt hab.2 hb.1.2⟩,
      lt_of_le_of_lt hab.2 (lt_of_lt_of_le hb.2
        (max_le_max le_rfl (Nat.sub_le_sub_left hab.1 k)))⟩
}
