import AFTD.Prelude

/-!
# binary_code_parity_class_card

Topic: combinatorics   Node: ba75d2399927

Provenance: helper lemma. arXiv:2611.04523, Proposition 3.1

For any integer n ≥ 1 and any parity ε : Fin 2, the set of words x : Fin n → Fin 2 whose sum of coordinates in Fin 2 equals ε has cardinality 2 ^ (n - 1).
-/

/-- The set of binary words of given coordinate-sum parity has cardinality 2^(n-1). -/
theorem binary_code_parity_class_card (n : ℕ) (hn : 1 ≤ n) (ε : Fin 2) : (Finset.univ.filter (fun x : Fin n → Fin 2 => (∑ i, x i) = ε)).card = 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
  classical
  let s : Finset (Fin (m + 1) → Fin 2) := Finset.univ.filter (fun x => (∑ i, x i) = ε)
  let t : Finset (Fin m → Fin 2) := Finset.univ
  have hcard : s.card = t.card := by
    refine Finset.card_bij (fun x _ => fun i : Fin m => x i.castSucc) ?_ ?_ ?_
    · intro x hx
      simp [t]
    · intro x hx y hy hxy
      have hxsum : (∑ i, x i) = ε := by
        simpa [s] using (Finset.mem_filter.mp hx).2
      have hysum : (∑ i, y i) = ε := by
        simpa [s] using (Finset.mem_filter.mp hy).2
      have hrest : (fun i : Fin m => x i.castSucc) = (fun i : Fin m => y i.castSucc) := hxy
      have hxy_sum : (∑ i : Fin m, x i.castSucc) = (∑ i : Fin m, y i.castSucc) := by
        rw [hrest]
      have hx' := hxsum
      rw [Fin.sum_univ_castSucc] at hx'
      have hy' := hysum
      rw [Fin.sum_univ_castSucc] at hy'
      have hlast : x (Fin.last m) = y (Fin.last m) := by
        have h1 : (∑ i : Fin m, x i.castSucc) + x (Fin.last m) =
            (∑ i : Fin m, y i.castSucc) + y (Fin.last m) := by
          rw [hx', hy']
        apply add_left_cancel (a := (∑ i : Fin m, x i.castSucc))
        rw [h1, ← hxy_sum]
      calc
        x = Fin.snoc (Fin.init x) (x (Fin.last m)) := (Fin.snoc_init_self x).symm
        _ = Fin.snoc (fun i : Fin m => x i.castSucc) (x (Fin.last m)) := by rfl
        _ = Fin.snoc (fun i : Fin m => y i.castSucc) (y (Fin.last m)) := by rw [hrest, hlast]
        _ = Fin.snoc (Fin.init y) (y (Fin.last m)) := by rfl
        _ = y := Fin.snoc_init_self y
    · intro y hy
      let x : Fin (m + 1) → Fin 2 := Fin.snoc y (ε - ∑ i, y i)
      refine ⟨x, ?_, ?_⟩
      · have hsum : (∑ i : Fin (m + 1), x i) = ε := by
          dsimp [x]
          rw [Fin.sum_snoc]
          exact add_sub_cancel _ _
        simp [s, hsum]
      · funext i
        simp [x]
  rw [hcard]
  simp [t]
