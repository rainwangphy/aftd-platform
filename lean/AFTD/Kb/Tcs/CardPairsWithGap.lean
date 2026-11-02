import AFTD.Prelude

/-!
# card_pairs_with_gap

Topic: combinatorics   Node: 2bd368798569

Provenance: helper lemma. arXiv:2610.38368, Section 2

For integers 1 ≤ k ≤ n - 1, the number of pairs (i, j) in {0, ..., n-1}^2 with j - i = k is n - k.
-/

/-- The number of pairs in {0, ..., n-1}^2 with difference k is n - k. -/
theorem card_pairs_with_gap (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (n - 1)) :
    ((Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)).filter
      (fun ⟨i, j⟩ => (i : ℕ) + k = (j : ℕ))).card = n - k := by
  have hk_le : k ≤ n := by
    rw [Finset.mem_Icc] at hk
    omega
  let s := ((Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)).filter
      (fun ⟨i, j⟩ => (i : ℕ) + k = (j : ℕ)))
  let t : Finset (Fin (n - k)) := Finset.univ
  have ht_card : t.card = n - k := by rw [Finset.card_univ, Fintype.card_fin]
  rw [← ht_card]
  refine Finset.card_bij' (s := s) (t := t)
    (fun p hp => ⟨p.1.1, by
      have hp' : (p.1 : ℕ) + k = (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
      have hj : (p.2 : ℕ) < n := p.2.2
      omega⟩)
    (fun a ha => (⟨a.1, by omega⟩, ⟨a.1 + k, by omega⟩))
    (fun a ha => Finset.mem_univ _)
    (fun a ha => by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      rfl)
    (fun ⟨i, j⟩ hp => by
      have hp' : (i : ℕ) + k = (j : ℕ) := (Finset.mem_filter.mp hp).2
      ext
      · rfl
      · exact hp')
    (fun a ha => by
      ext
      rfl)
