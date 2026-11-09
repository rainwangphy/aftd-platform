import AFTD.Prelude
import AFTD.Kb.Tcs.SprValue
import AFTD.Kb.Optimization.PartialAssignmentLe
import AFTD.Kb.Tcs.SprSignCount
import AFTD.Kb.Tcs.SprMove

/-!
# spr_minimax_sign_deletion_monotonicity

Topic: learning   Node: d66cf425ef69

Provenance: formalization of a published result. Source: arXiv:2410.07623, Section 2.2

In the sign-preservation-with-reuse game, the minimax value is monotone under adding existing signs: for every number n of ordered cells, remaining horizon r, and boards b, b' : Fin n → Option Bool where b' is obtained from b by turning a subset of signs into empty cells (partial_assignment_le b' b), spr_value n r b' ≤ spr_value n r b.
-/

noncomputable def spr_minimax_sign_deletion_monotonicity_del_set {n : ℕ} (j : Fin n) (b : Fin n → Option Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i < j ∧ b i = some false) ∨ (j < i ∧ b i = some true))

noncomputable def spr_minimax_sign_deletion_monotonicity_opt_set {n : ℕ} (j : Fin n) (b : Fin n → Option Bool) : Finset (Finset (Fin n) × Bool) :=
  Finset.univ.filter (fun p => ∀ i ∈ p.1, (i < j ∧ b i = some false) ∨ (j < i ∧ b i = some true))

lemma spr_minimax_sign_deletion_monotonicity_opt_set_nonempty {n : ℕ} (j : Fin n) (b : Fin n → Option Bool) :
    (spr_minimax_sign_deletion_monotonicity_opt_set j b).Nonempty :=
  ⟨(∅, true), by
    simp only [spr_minimax_sign_deletion_monotonicity_opt_set, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi; exact absurd hi (Finset.notMem_empty i)⟩

lemma spr_minimax_sign_deletion_monotonicity_pal_of_pointwise {n : ℕ} {β γ : Fin n → Option Bool}
    (h : ∀ i, β i = none ∨ β i = γ i) : partial_assignment_le β γ := by
  intro i v hv
  rcases h i with h1 | h1
  · rw [h1] at hv; exact absurd hv (by simp)
  · rw [← h1]; exact hv

lemma spr_minimax_sign_deletion_monotonicity_sign_count_le {n : ℕ} {b b' : Fin n → Option Bool}
    (hle : partial_assignment_le b' b) :
    spr_sign_count b' ≤ spr_sign_count b := by
  unfold spr_sign_count
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [Option.isSome_iff_exists] at hi ⊢
  obtain ⟨v, hv⟩ := hi
  exact ⟨v, hle i v hv⟩

lemma spr_minimax_sign_deletion_monotonicity_move_delete_le {n : ℕ} (b : Fin n → Option Bool) (j : Fin n)
    (R D : Finset (Fin n)) (s : Bool) (hRD : R ⊆ D) :
    partial_assignment_le (spr_move b j D s) (spr_move b j R s) := by
  apply spr_minimax_sign_deletion_monotonicity_pal_of_pointwise
  intro i
  simp only [spr_move]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [if_neg hij]
    by_cases hiD : i ∈ D
    · left; simp only [if_pos hiD]
    · right
      have hiR : i ∉ R := fun h => hiD (hRD h)
      simp only [if_neg hiD, if_neg hiR]

lemma spr_minimax_sign_deletion_monotonicity_move_cross_le {n : ℕ} {b b' : Fin n → Option Bool}
    (hle : partial_assignment_le b' b) (j : Fin n) (s : Bool) :
    partial_assignment_le (spr_move b' j (spr_minimax_sign_deletion_monotonicity_del_set j b') s)
      (spr_move b j (spr_minimax_sign_deletion_monotonicity_del_set j b) s) := by
  intro i v hv
  simp only [spr_move] at hv ⊢
  by_cases hij : i = j
  · subst hij; simpa using hv
  · simp only [if_neg hij] at hv ⊢
    by_cases hiD' : i ∈ spr_minimax_sign_deletion_monotonicity_del_set j b'
    · simp only [if_pos hiD'] at hv; exact absurd hv (by simp)
    · simp only [if_neg hiD'] at hv
      by_cases hiD : i ∈ spr_minimax_sign_deletion_monotonicity_del_set j b
      · exfalso
        have hb' : b' i = some v := hv
        have hb : b i = some v := hle i v hb'
        simp only [spr_minimax_sign_deletion_monotonicity_del_set, Finset.mem_filter, Finset.mem_univ, true_and] at hiD hiD'
        rw [hb] at hiD
        rw [hb'] at hiD'
        exact hiD' hiD
      · simp only [if_neg hiD]; exact hle i v hv

lemma spr_minimax_sign_deletion_monotonicity_move_none_pal {n : ℕ} {b b' : Fin n → Option Bool}
    (hle : partial_assignment_le b' b) (j : Fin n) {v : Bool} (hv : b j = some v) :
    partial_assignment_le (spr_move b' j ∅ v) b := by
  apply spr_minimax_sign_deletion_monotonicity_pal_of_pointwise
  intro i
  by_cases hij : i = j
  · subst hij
    right
    simp only [spr_move]
    exact hv.symm
  · simp only [spr_move, if_neg hij, Finset.notMem_empty, if_false]
    cases hbi : b' i with
    | none => left; rfl
    | some c => right; exact (hle i c hbi).symm

lemma spr_minimax_sign_deletion_monotonicity_horizon_mono {n : ℕ} (r : ℕ) (b : Fin n → Option Bool) :
    spr_value n r b ≤ spr_value n (r+1) b := by
  induction r generalizing b with
  | zero => rw [spr_value.eq_1, spr_value.eq_2]; exact Nat.le_max_left _ _
  | succ k ih =>
    rw [spr_value.eq_2, spr_value.eq_2]
    apply Nat.max_le.2
    refine ⟨Nat.le_max_left _ _, ?_⟩
    apply le_trans (Finset.sup_le ?_) (Nat.le_max_right _ _)
    intro j hj
    refine le_trans ?_ (Finset.le_sup hj)
    apply Finset.le_inf'
    intro p hp
    exact le_trans (Finset.inf'_le _ hp) (ih _)

/-- Sign deletion monotonicity of the minimax value in the SPR game (OP-1114). -/
theorem spr_minimax_sign_deletion_monotonicity (n r : ℕ) (b b' : Fin n → Option Bool)
    (hle : partial_assignment_le b' b) :
    spr_value n r b' ≤ spr_value n r b := by
  induction r generalizing b b' with
  | zero =>
    rw [spr_value.eq_1, spr_value.eq_1]
    exact spr_minimax_sign_deletion_monotonicity_sign_count_le hle
  | succ k ih =>
    conv_lhs => rw [spr_value.eq_2]
    apply Nat.max_le.2
    refine ⟨?_, ?_⟩
    · refine le_trans (spr_minimax_sign_deletion_monotonicity_sign_count_le hle) ?_
      rw [spr_value.eq_2]
      exact Nat.le_max_left _ _
    · apply Finset.sup_le
      intro j hj
      by_cases hbj : b j = none
      · rw [spr_value.eq_2]
        have hB : (Finset.univ : Finset Bool).Nonempty := ⟨true, Finset.mem_univ _⟩
        have h1 : (spr_minimax_sign_deletion_monotonicity_opt_set j b').inf'
              (spr_minimax_sign_deletion_monotonicity_opt_set_nonempty j b')
              (fun p => spr_value n k (spr_move b' j p.1 p.2))
            ≤ (Finset.univ : Finset Bool).inf' hB
              (fun s => spr_value n k (spr_move b' j (spr_minimax_sign_deletion_monotonicity_del_set j b') s)) := by
          refine Finset.le_inf' hB (fun s => spr_value n k (spr_move b' j (spr_minimax_sign_deletion_monotonicity_del_set j b') s)) ?_
          intro s hs
          refine Finset.inf'_le (f := fun p : Finset (Fin n) × Bool => spr_value n k (spr_move b' j p.1 p.2)) (b := (spr_minimax_sign_deletion_monotonicity_del_set j b', s)) ?_
          simp only [spr_minimax_sign_deletion_monotonicity_opt_set, Finset.mem_filter, Finset.mem_univ, true_and]
          intro i hi
          simp only [spr_minimax_sign_deletion_monotonicity_del_set, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact hi
        have h2 : (Finset.univ : Finset Bool).inf' hB
              (fun s => spr_value n k (spr_move b' j (spr_minimax_sign_deletion_monotonicity_del_set j b') s))
            ≤ (Finset.univ : Finset Bool).inf' hB
              (fun s => spr_value n k (spr_move b j (spr_minimax_sign_deletion_monotonicity_del_set j b) s)) := by
          refine Finset.le_inf' hB (fun s => spr_value n k (spr_move b j (spr_minimax_sign_deletion_monotonicity_del_set j b) s)) ?_
          intro s hs
          refine le_trans (Finset.inf'_le (f := fun t => spr_value n k (spr_move b' j (spr_minimax_sign_deletion_monotonicity_del_set j b') t)) (Finset.mem_univ s)) ?_
          exact ih _ _ (spr_minimax_sign_deletion_monotonicity_move_cross_le hle j s)
        have h3 : (Finset.univ : Finset Bool).inf' hB
              (fun s => spr_value n k (spr_move b j (spr_minimax_sign_deletion_monotonicity_del_set j b) s))
            ≤ (spr_minimax_sign_deletion_monotonicity_opt_set j b).inf'
              (spr_minimax_sign_deletion_monotonicity_opt_set_nonempty j b)
              (fun p => spr_value n k (spr_move b j p.1 p.2)) := by
          refine Finset.le_inf' (spr_minimax_sign_deletion_monotonicity_opt_set_nonempty j b)
            (fun p => spr_value n k (spr_move b j p.1 p.2)) ?_
          intro p hp
          obtain ⟨Rf, s⟩ := p
          simp only [spr_minimax_sign_deletion_monotonicity_opt_set, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hRD : Rf ⊆ spr_minimax_sign_deletion_monotonicity_del_set j b := by
            intro i hi
            simp only [spr_minimax_sign_deletion_monotonicity_del_set, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hp i hi
          refine le_trans (Finset.inf'_le (f := fun t => spr_value n k (spr_move b j (spr_minimax_sign_deletion_monotonicity_del_set j b) t)) (Finset.mem_univ s)) ?_
          exact ih _ _ (spr_minimax_sign_deletion_monotonicity_move_delete_le b j Rf (spr_minimax_sign_deletion_monotonicity_del_set j b) s hRD)
        have h4 : (spr_minimax_sign_deletion_monotonicity_opt_set j b).inf'
              (spr_minimax_sign_deletion_monotonicity_opt_set_nonempty j b)
              (fun p => spr_value n k (spr_move b j p.1 p.2))
            ≤ max (spr_sign_count b)
                ((Finset.univ.filter (fun j => b j = none)).sup
                  (fun j => (spr_minimax_sign_deletion_monotonicity_opt_set j b).inf'
                    (spr_minimax_sign_deletion_monotonicity_opt_set_nonempty j b)
                    (fun p => spr_value n k (spr_move b j p.1 p.2)))) := by
          refine le_trans (Finset.le_sup (f := fun j' => (spr_minimax_sign_deletion_monotonicity_opt_set j' b).inf'
              (spr_minimax_sign_deletion_monotonicity_opt_set_nonempty j' b)
              (fun p => spr_value n k (spr_move b j' p.1 p.2))) ?_) (Nat.le_max_right _ _)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbj⟩
        exact le_trans h1 (le_trans h2 (le_trans h3 h4))
      · obtain ⟨v, hv⟩ : ∃ v, b j = some v := by
          cases h : b j with
          | none => exact absurd h hbj
          | some v => exact ⟨v, rfl⟩
        refine le_trans ?_ (spr_minimax_sign_deletion_monotonicity_horizon_mono k b)
        refine le_trans ?_ (ih _ _ (spr_minimax_sign_deletion_monotonicity_move_none_pal hle j hv))
        refine Finset.inf'_le (f := fun p : Finset (Fin n) × Bool => spr_value n k (spr_move b' j p.1 p.2)) (b := (∅, v)) ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi; exact absurd hi (Finset.notMem_empty i)
