import AFTD.Prelude

/-!
# exists_bin_packing_of_total_capacity_ge

Topic: fair_division   Node: 566d766fdcf5

Provenance: formalization of a published result. Source: arXiv:2610.15520 (Improving the bounds on approximating weighted maximin shares of chores), Lemma 5.4.

If b bins have capacities C_j and current loads L_j ≤ C_j with Σ L_j + (m + b)η ≤ Σ C_j (η > 0), then m items of size η can be added to the bins without exceeding any capacity.
-/

theorem exists_bin_packing_of_total_capacity_ge {b m : ℕ} (C L : Fin b → ℝ) (η : ℝ)
    (hη : 0 < η) (hL : ∀ j, L j ≤ C j) (h : ∑ j, L j + (m + b) * η ≤ ∑ j, C j) :
    ∃ f : Fin m → Fin b, ∀ j, L j + (Finset.univ.filter (fun i => f i = j)).card * η ≤ C j := by
  revert L
  induction m with
  | zero =>
    intro L hL h
    refine ⟨fun i => i.elim0, ?_⟩
    intro j
    have : (Finset.univ.filter (fun (i : Fin 0) => (fun _ => i.elim0) i = j)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i
      exact i.elim0
    rw [this, Finset.card_empty, Nat.cast_zero, MulZeroClass.zero_mul, add_zero]
    exact hL j
  | succ m ih =>
    intro L hL h
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at h
      have hpos : 0 < ((m + 1 : ℝ) * η) := by positivity
      push_cast at h
      linarith
    · have hex : ∃ j₀ : Fin b, L j₀ + η ≤ C j₀ := by
        by_contra! h_all
        have h_ne : (Finset.univ : Finset (Fin b)).Nonempty :=
          Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hb)
        have h1 : ∑ j, C j < ∑ j, (L j + η) := Finset.sum_lt_sum_of_nonempty h_ne (fun j _ => h_all j)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
        have h_exp : (↑(m + 1) + ↑b : ℝ) * η = (m : ℝ) * η + η + (b : ℝ) * η := by
          push_cast
          ring
        nlinarith
      rcases hex with ⟨j₀, hj₀⟩
      set L' := Function.update L j₀ (L j₀ + η) with hL'_def
      have hL' : ∀ j, L' j ≤ C j := by
        intro j
        by_cases hj : j = j₀
        · subst hj
          rw [hL'_def, Function.update_self]
          exact hj₀
        · rw [hL'_def, Function.update_of_ne hj]
          exact hL j
      have h_sum' : ∑ j, L' j + ((m : ℝ) + (b : ℝ)) * η ≤ ∑ j, C j := by
        have hi : j₀ ∈ (Finset.univ : Finset (Fin b)) := Finset.mem_univ j₀
        have h1 := Finset.sum_update_of_mem hi L (L j₀ + η)
        rw [Finset.sdiff_singleton_eq_erase] at h1
        have h2 := Finset.add_sum_erase Finset.univ L hi
        have h_sum : ∑ j, L' j = (∑ j, L j) + η := by
          rw [hL'_def, h1]
          linarith
        have : (↑(m + 1) + ↑b : ℝ) * η = (↑m + ↑b) * η + η := by
          push_cast
          ring
        linarith
      rcases ih L' hL' h_sum' with ⟨f', hf'⟩
      refine ⟨Fin.cons (α := fun _ => Fin b) j₀ f', ?_⟩
      intro j
      have h_card := @Fin.card_filter_univ_succ m (fun (i : Fin (m + 1)) => (Fin.cons (α := fun _ => Fin b) j₀ f') i = j) _
      simp only [Fin.cons_zero, Fin.cons_succ] at h_card
      have h_ih_j := hf' j
      by_cases hj : j₀ = j
      · subst hj
        rw [hL'_def, Function.update_self] at h_ih_j
        rw [h_card, if_pos rfl]
        push_cast
        linarith
      · rw [hL'_def, Function.update_of_ne (Ne.symm hj)] at h_ih_j
        rw [h_card, if_neg hj]
        exact h_ih_j
