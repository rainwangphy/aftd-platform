import AFTD.Prelude

/-!
# path_strong_five_edge_coloring_with_prescribed_endpoints

Topic: graphs   Node: 8b25d83124c0

Provenance: helper lemma. step towards subcubic_three_vertices_max_degree_le_one_exists_rich_neighbor_five_coloring

For any path of length l ≥ 4 and any colors a, b in Fin 5, there is a strong 5-edge-coloring with prescribed endpoint colors a and b.
-/

lemma path_strong_five_edge_coloring_with_prescribed_endpoints_fin5_exists_ne_three :
    ∀ p q r : Fin 5, ∃ x : Fin 5, x ≠ p ∧ x ≠ q ∧ x ≠ r := by
  decide

lemma path_strong_five_edge_coloring_with_prescribed_endpoints_base_four :
    ∀ a b : Fin 5, ∃ c : Fin 4 → Fin 5,
      c ⟨0, by omega⟩ = a ∧
      c ⟨3, by omega⟩ = b ∧
      ∀ i j : Fin 4, (i.val < j.val ∧ j.val ≤ i.val + 2) → c i ≠ c j := by
  decide

lemma path_strong_five_edge_coloring_with_prescribed_endpoints_extend_one
    (L : ℕ) (hL : 4 ≤ L) (a b' : Fin 5)
    (c : Fin L → Fin 5)
    (hc0 : c ⟨0, by omega⟩ = a)
    (hc : ∀ i j : Fin L, (i.val < j.val ∧ j.val ≤ i.val + 2) → c i ≠ c j) :
    ∃ c' : Fin (L+1) → Fin 5,
      c' ⟨0, by omega⟩ = a ∧
      c' ⟨L, by omega⟩ = b' ∧
      ∀ i j : Fin (L+1), (i.val < j.val ∧ j.val ≤ i.val + 2) → c' i ≠ c' j := by
  let iL3 : Fin L := ⟨L - 3, by omega⟩
  let iL4 : Fin L := ⟨L - 4, by omega⟩
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    path_strong_five_edge_coloring_with_prescribed_endpoints_fin5_exists_ne_three
      (c iL3) (c iL4) b'
  obtain ⟨y, hy1, hy2, hy3⟩ :=
    path_strong_five_edge_coloring_with_prescribed_endpoints_fin5_exists_ne_three
      x (c iL3) b'
  let c' : Fin (L+1) → Fin 5 := fun i =>
    if h : i.val < L - 2 then c ⟨i.val, by omega⟩
    else if i.val = L - 2 then x
    else if i.val = L - 1 then y
    else b'
  have hc'_prefix : ∀ {i : Fin (L+1)} (hi : i.val < L - 2), c' i = c ⟨i.val, by omega⟩ := by
    intro i hi
    simp only [c']
    rw [dif_pos hi]
  have hc'_x : ∀ {i : Fin (L+1)}, i.val = L - 2 → c' i = x := by
    intro i hi
    simp only [c']
    rw [dif_neg (by omega), if_pos hi]
  have hc'_y : ∀ {i : Fin (L+1)}, i.val = L - 1 → c' i = y := by
    intro i hi
    simp only [c']
    rw [dif_neg (by omega), if_neg (by omega), if_pos hi]
  have hc'_z : ∀ {i : Fin (L+1)}, i.val = L → c' i = b' := by
    intro i hi
    simp only [c']
    rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨c', ?_, ?_, ?_⟩
  · simp [c', show 0 < L - 2 by omega, hc0]
  · simp [c', show ¬ L < L - 2 by omega, show L ≠ L - 2 by omega, show L ≠ L - 1 by omega]
  · intro i j hij
    by_cases hi : i.val < L - 2
    · have hci : c' i = c ⟨i.val, by omega⟩ := hc'_prefix hi
      by_cases hj : j.val < L - 2
      · have hcj : c' j = c ⟨j.val, by omega⟩ := hc'_prefix hj
        rw [hci, hcj]
        exact hc ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij
      · have hj_cases : j.val = L - 2 ∨ j.val = L - 1 := by omega
        rcases hj_cases with hj2 | hj1
        · have hcj : c' j = x := hc'_x hj2
          rw [hci, hcj]
          have hi_cases : i.val = L - 4 ∨ i.val = L - 3 := by omega
          rcases hi_cases with hi4 | hi3
          · have h_eq : c ⟨i.val, by omega⟩ = c iL4 := by
              congr 1
              apply Fin.ext
              simp [iL4]
              omega
            rw [h_eq]
            exact fun h => hx2 h.symm
          · have h_eq : c ⟨i.val, by omega⟩ = c iL3 := by
              congr 1
              apply Fin.ext
              simp [iL3]
              omega
            rw [h_eq]
            exact fun h => hx1 h.symm
        · have hcj : c' j = y := hc'_y hj1
          rw [hci, hcj]
          have hi3 : i.val = L - 3 := by omega
          have h_eq : c ⟨i.val, by omega⟩ = c iL3 := by
            congr 1
            apply Fin.ext
            simp [iL3]
            omega
          rw [h_eq]
          exact Ne.symm hy2
    · have hi_cases : i.val = L - 2 ∨ i.val = L - 1 ∨ i.val = L := by omega
      rcases hi_cases with hi2 | hi1 | hiL
      · have hci : c' i = x := hc'_x hi2
        have hj_cases : j.val = L - 1 ∨ j.val = L := by omega
        rcases hj_cases with hj1 | hjL
        · have hcj : c' j = y := hc'_y hj1
          rw [hci, hcj]
          exact Ne.symm hy1
        · have hcj : c' j = b' := hc'_z hjL
          rw [hci, hcj]
          exact hx3
      · have hci : c' i = y := hc'_y hi1
        have hjL : j.val = L := by omega
        have hcj : c' j = b' := hc'_z hjL
        rw [hci, hcj]
        exact hy3
      · omega

lemma path_strong_five_edge_coloring_with_prescribed_endpoints_add_four
    (n : ℕ) (a b : Fin 5) :
    ∃ c : Fin (n + 4) → Fin 5,
      c ⟨0, by omega⟩ = a ∧
      c ⟨n + 3, by omega⟩ = b ∧
      ∀ i j : Fin (n + 4), (i.val < j.val ∧ j.val ≤ i.val + 2) → c i ≠ c j := by
  induction n with
  | zero =>
      simpa using path_strong_five_edge_coloring_with_prescribed_endpoints_base_four a b
  | succ n ih =>
      obtain ⟨c, hc0, _hcend, hcvalid⟩ := ih
      obtain ⟨c', hc'0, hc'end, hc'valid⟩ :=
        path_strong_five_edge_coloring_with_prescribed_endpoints_extend_one
          (L := n + 4) (by omega) a b c hc0 hcvalid
      refine ⟨c', hc'0, ?_, hc'valid⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc'end

/-- Lemma 2.3 of arXiv:2610.21868: strong 5-edge-coloring of paths of length at least 4 with prescribed endpoints. -/
theorem path_strong_five_edge_coloring_with_prescribed_endpoints (l : ℕ) (hl : 4 ≤ l)
    (a b : Fin 5) :
    ∃ c : Fin l → Fin 5,
      c ⟨0, by omega⟩ = a ∧
      c ⟨l - 1, by omega⟩ = b ∧
      ∀ (i j : Fin l), (i.val < j.val ∧ j.val ≤ i.val + 2) → c i ≠ c j := by
  obtain ⟨c, hc0, hcend, hcvalid⟩ :=
    path_strong_five_edge_coloring_with_prescribed_endpoints_add_four (l - 4) a b
  have hlen : l - 4 + 4 = l := by omega
  let c' : Fin l → Fin 5 := fun i => c (Fin.cast hlen.symm i)
  refine ⟨c', ?_, ?_, ?_⟩
  · change c (Fin.cast hlen.symm ⟨0, by omega⟩) = a
    have h0 : Fin.cast hlen.symm (⟨0, by omega⟩ : Fin l) = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [Fin.cast]
    rw [h0]
    exact hc0
  · change c (Fin.cast hlen.symm ⟨l - 1, by omega⟩) = b
    have hlast : Fin.cast hlen.symm (⟨l - 1, by omega⟩ : Fin l) = ⟨l - 4 + 3, by omega⟩ := by
      apply Fin.ext
      simp [Fin.cast]
      omega
    rw [hlast]
    simpa using hcend
  · intro i j hij
    change c (Fin.cast hlen.symm i) ≠ c (Fin.cast hlen.symm j)
    apply hcvalid
    simpa [Fin.cast] using hij
