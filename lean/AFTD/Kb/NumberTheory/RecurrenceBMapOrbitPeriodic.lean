import AFTD.Prelude
import AFTD.Kb.NumberTheory.RecurrenceBMap
import AFTD.Kb.NumberTheory.RecurrenceBMapBijective

/-!
# recurrence_b_map_orbit_periodic

Topic: elementary_number_theory   Node: 5bda2ede0ebf

Provenance: helper lemma. arXiv:2610.34300 Proposition 7

For any integer k ≥ 2, every orbit of the transition map of recurrence (B) on (ℤ/3ℤ)^k is purely periodic: for every state w, there exists m > 0 such that the m-th iterate of the map on w is w.
-/

/-- Pure periodicity of orbits of recurrence B for k ≥ 2. -/
theorem recurrence_b_map_orbit_periodic (k : ℕ) (hk : 2 ≤ k) (w : Fin k → ZMod 3) : ∃ m > 0, (recurrence_b_map k)^[m] w = w := by
  have hinj : Function.Injective (recurrence_b_map k) :=
    (recurrence_b_map_bijective k hk).1
  let N := Fintype.card (Fin k → ZMod 3)
  have hcard : Fintype.card (Fin (N + 1)) > Fintype.card (Fin k → ZMod 3) := by
    simp [N]
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (N + 1) => (recurrence_b_map k)^[(i : ℕ)] w) hcard
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(j : ℕ) - (i : ℕ), Nat.sub_pos_of_lt (Fin.lt_def.mp hlt), ?_⟩
    have hji : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by
      exact (Nat.add_sub_of_le (le_of_lt (Fin.lt_def.mp hlt))).symm
    have hcancel : (recurrence_b_map k)^[(i : ℕ)] ((recurrence_b_map k)^[((j : ℕ) - (i : ℕ))] w)
        = (recurrence_b_map k)^[(i : ℕ)] w := by
      rw [← Function.iterate_add_apply, ← hji]
      exact heq.symm
    exact (Function.Injective.iterate hinj (i : ℕ)) hcancel
  · refine ⟨(i : ℕ) - (j : ℕ), Nat.sub_pos_of_lt (Fin.lt_def.mp hlt), ?_⟩
    have hij : (i : ℕ) = (j : ℕ) + ((i : ℕ) - (j : ℕ)) := by
      exact (Nat.add_sub_of_le (le_of_lt (Fin.lt_def.mp hlt))).symm
    have hcancel : (recurrence_b_map k)^[(j : ℕ)] ((recurrence_b_map k)^[((i : ℕ) - (j : ℕ))] w)
        = (recurrence_b_map k)^[(j : ℕ)] w := by
      rw [← Function.iterate_add_apply, ← hij]
      exact heq
    exact (Function.Injective.iterate hinj (j : ℕ)) hcancel
