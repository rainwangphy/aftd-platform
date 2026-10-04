import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.GameTheoryEconomics.HasBinaryMarginals
import AFTD.Kb.GameTheoryEconomics.IsPmmsFair
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.CappedCountMarginal

/-!
# pmms_fair_not_imp_mms_fair

Topic: fair_division   Node: 8e034309f4af

Open problem 4 of arXiv:2502.02815 has a negative answer: for submodular goods with binary marginals and equal entitlements, pairwise MMS does not imply MMS. Example: three agents with the same valuation min(#X, 1) + min(#Y, 2) on six goods, X = {0,1,2}, Y = {3,4,5}; the allocation {0,1,3}, {2}, {4,5} is pairwise-MMS-fair but the second agent gets 1 < MMS = 2.
-/

theorem pmms_fair_not_imp_mms_fair :
    ¬ ∀ (n m : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
      (∀ i, v i ∅ = 0 ∧ is_submodular (v i) ∧ has_binary_marginals (v i)) →
      ∀ σ : Fin m → Fin n, (∀ i, is_pmms_fair v σ i) →
        ∀ i, maximin_share (v i) n ≤ v i (bundle_of σ i) := by
  intro h
  -- six goods in two colours, X = {0,1,2} and Y = {3,4,5};
  -- every agent values a bundle by min(#X, 1) + min(#Y, 2)
  let vN : Finset (Fin 6) → ℕ := fun S =>
    min (S.filter fun x => x.val < 3).card 1 + min (S.filter fun x => ¬ x.val < 3).card 2
  let v : Fin 3 → Finset (Fin 6) → ℝ := fun _ S => (vN S : ℝ)
  let σ : Fin 6 → Fin 3 := ![0, 0, 1, 0, 2, 2]
  have hclass : ∀ i, v i ∅ = 0 ∧ is_submodular (v i) ∧ has_binary_marginals (v i) := by
    intro i
    refine ⟨by simp [v, vN], ?_, ?_⟩
    · intro S T j hST hj
      have h1 := (capped_count_marginal (fun x : Fin 6 => x.val < 3) 1 S T j hST hj).1
      have h2 := (capped_count_marginal (fun x : Fin 6 => ¬ x.val < 3) 2 S T j hST hj).1
      simp only [v, vN]
      have : ((vN (insert j T) + vN S : ℕ) : ℝ) ≤ ((vN (insert j S) + vN T : ℕ) : ℝ) := by
        exact_mod_cast (by simp only [vN]; omega)
      push_cast at this
      simp only [vN] at this
      linarith
    · intro S j hj
      have h1 := capped_count_marginal (fun x : Fin 6 => x.val < 3) 1 S S j (le_refl S) hj
      have h2 := capped_count_marginal (fun x : Fin 6 => ¬ x.val < 3) 2 S S j (le_refl S) hj
      simp only [v, vN]
      by_cases hx : j.val < 3
      · have e2 := h2.2.2 (by simpa using hx)
        rcases h1.2.1 with e1 | e1
        · left; rw [e1, e2]
        · right; rw [e1, e2]; push_cast; ring
      · have e1 := h1.2.2 hx
        rcases h2.2.1 with e2 | e2
        · left; rw [e1, e2]
        · right; rw [e1, e2]; push_cast; ring
  -- the allocation {0,1,3}, {2}, {4,5} is pairwise-MMS-fair to everyone
  have hpmms : ∀ i, is_pmms_fair v σ i := by
    have key : ∀ i j : Fin 3, j ≠ i → ∀ T : Finset (Fin 6),
        T ⊆ bundle_of σ i ∪ bundle_of σ j →
        min (vN T) (vN ((bundle_of σ i ∪ bundle_of σ j) \ T)) ≤ vN (bundle_of σ i) := by
      decide
    intro i j hji
    have : Nonempty {T : Finset (Fin 6) // T ⊆ bundle_of σ i ∪ bundle_of σ j} :=
      ⟨⟨∅, Finset.empty_subset _⟩⟩
    apply ciSup_le
    intro T
    have := key i j hji T.1 T.2
    simp only [v]
    rw [← Nat.cast_min]
    exact_mod_cast this
  -- but agent 1 holds {2}, worth 1, while the partition {0,3}, {1,4}, {2,5} gives everyone 2
  have hmms := h 3 6 v hclass σ hpmms 1
  have hb1 : vN (bundle_of σ 1) = 1 := by decide
  let P : Fin 6 → Fin 3 := ![0, 1, 2, 0, 1, 2]
  have hP : ∀ k, vN (bundle_of P k) = 2 := by decide
  have hge : (2 : ℝ) ≤ maximin_share (v 1) 3 := by
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove P)
    have : Nonempty (Fin 3) := ⟨0⟩
    exact le_ciInf fun k => by simp only [v]; rw [hP k]; norm_num
  simp only [v] at hmms
  rw [hb1] at hmms
  norm_num at hmms
  linarith
