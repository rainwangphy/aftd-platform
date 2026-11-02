import AFTD.Prelude

/-!
# cross_pair_orientation_sum_capacity

Topic: graphs   Node: 284c9f50b68d

Provenance: helper lemma. Auxiliary-graph transfer and counting steps for the OP-110 campaign.

A two-row, 2s−1-column orientation table cannot satisfy the displayed row and column capacity bounds when s is at least three.
-/

theorem cross_pair_orientation_sum_capacity (s : ℕ) (hs : 3 ≤ s)
    (P : Fin 2 → Fin (2*s-1) → Prop) [∀ i j, Decidable (P i j)]
    (T : Finset (Fin (2*s-1))) (hT : T.card ≤ s-1)
    (hrow : ∀ i, (∑ j, if P i j then 1 else 0) ≤ 1)
    (hcol : ∀ j, (∑ i, if P i j then 0 else 1) ≤ 1 + if j ∈ T then 1 else 0) : False := by
  classical
  have hrows : (∑ i, ∑ j, if P i j then 1 else 0) ≤ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
    simpa using h
  have hcols : (∑ j, ∑ i, if P i j then 0 else 1) ≤ 2*s-1 + T.card := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcol j)
    simpa [Finset.sum_add_distrib] using h
  have htotal : (∑ i, ∑ j, if P i j then 1 else 0) +
      (∑ j, ∑ i, if P i j then 0 else 1) = 2 * (2*s-1) := by
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun j i => if P i j then 0 else 1)]
    calc
      _ = ∑ i : Fin 2, ∑ j : Fin (2*s-1),
          ((if P i j then 1 else 0) + (if P i j then 0 else 1)) := by
            simp only [Finset.sum_add_distrib]
      _ = ∑ _i : Fin 2, ∑ _j : Fin (2*s-1), (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            split_ifs <;> omega
      _ = 2 * (2*s-1) := by simp
  omega
