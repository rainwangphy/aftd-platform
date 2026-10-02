import AFTD.Prelude

/-!
# capped_count_marginal

Topic: fair_division   Node: afebf7a366c4

For S inside T and j outside T, the capped count S -> min(#{x in S : p x}, c) has a marginal value at T at most its marginal value at S, its marginal values are 0 or 1, and adding an item outside p changes nothing.
-/

/-- `S ↦ min (#{x ∈ S | p x}) c`: a capped count, the rank of a one-block partition matroid. -/
theorem capped_count_marginal {m : ℕ} (p : Fin m → Prop) [DecidablePred p] (c : ℕ)
    (S T : Finset (Fin m)) (j : Fin m) (hST : S ⊆ T) (hj : j ∉ T) :
    min ((insert j T).filter p).card c + min (S.filter p).card c ≤
        min ((insert j S).filter p).card c + min (T.filter p).card c ∧
      (min ((insert j S).filter p).card c = min (S.filter p).card c ∨
        min ((insert j S).filter p).card c = min (S.filter p).card c + 1) ∧
      (¬ p j → min ((insert j S).filter p).card c = min (S.filter p).card c) := by
  have hjS : j ∉ S := fun h => hj (hST h)
  have hle : (S.filter p).card ≤ (T.filter p).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hST)
  by_cases hpj : p j
  · rw [Finset.filter_insert, if_pos hpj, Finset.filter_insert, if_pos hpj,
      Finset.card_insert_of_notMem (fun h => hj (Finset.mem_filter.1 h).1),
      Finset.card_insert_of_notMem (fun h => hjS (Finset.mem_filter.1 h).1)]
    refine ⟨by omega, by omega, fun h => absurd hpj h⟩
  · rw [Finset.filter_insert, if_neg hpj, Finset.filter_insert, if_neg hpj]
    exact ⟨le_refl _ |>.trans (by omega), Or.inl rfl, fun _ => rfl⟩
