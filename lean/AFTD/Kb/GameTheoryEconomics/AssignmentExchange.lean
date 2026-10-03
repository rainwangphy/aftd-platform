import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MonroePermSwapFinsets

/-!
# assignment_exchange

Topic: social_choice   Node: 37bc1835ff22

Generic exchange step: for an assignment π of voters to β, a set S of voters each satisfied by c′ but not by π, and the renaming c ↦ c′ after a suitable permutation σ of the voters, the number of satisfied voters grows by at least min(|π⁻¹(c)|, |S|) - |π⁻¹(c) \ S|.
-/

/-- The generic exchange step behind the Monroe arguments. Let `π` assign voters to `β`, let every member of `S` be satisfied by `c'` (`g i c'`) but not by `π`, and rename `c` to `c'` after a suitable permutation `σ` of the voters. Then the number of satisfied voters grows by at least `min(|π⁻¹(c)|, |S|) - |π⁻¹(c) \ S|`. -/
theorem assignment_exchange {n : ℕ} {β : Type*} [DecidableEq β] (g : Fin n → β → Prop)
    [∀ i b, Decidable (g i b)] (π : Fin n → β) (c c' : β) (S : Finset (Fin n))
    (hSa : ∀ i ∈ S, g i c') (hun : ∀ i ∈ S, ¬ g i (π i)) :
    ∃ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter fun i => g i (π i)).card +
          min (Finset.univ.filter fun i => π i = c).card S.card ≤
        (Finset.univ.filter fun i => g i (if π (σ i) = c then c' else π (σ i))).card +
          ((Finset.univ.filter fun i => π i = c).filter fun i => i ∉ S).card := by
  set R := Finset.univ.filter fun i => π i = c with hR
  set P := R.filter fun i => i ∉ S with hP
  set Q := S.filter fun i => π i ≠ c with hQ
  set T := R.filter fun i => i ∈ S with hT
  obtain ⟨P', hP'P, hP'c⟩ := Finset.exists_subset_card_eq (min_le_left P.card Q.card)
  obtain ⟨Q', hQ'Q, hQ'c⟩ := Finset.exists_subset_card_eq (min_le_right P.card Q.card)
  have memP : ∀ v, v ∈ P ↔ π v = c ∧ v ∉ S := by intro v; simp [hP, hR]
  have memQ : ∀ v, v ∈ Q ↔ v ∈ S ∧ π v ≠ c := by intro v; simp [hQ]
  have memT : ∀ v, v ∈ T ↔ π v = c ∧ v ∈ S := by intro v; simp [hT, hR]
  have hdisj : Disjoint P' Q' := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact ((memP v).1 (hP'P h1)).2 ((memQ v).1 (hQ'Q h2)).1
  obtain ⟨σ, h1, h2, h3⟩ := monroe_perm_swap_finsets P' Q' hdisj (hP'c.trans hQ'c.symm)
  let ρ : β → β := fun x => if x = c then c' else x
  refine ⟨σ, ?_⟩
  show (Finset.univ.filter fun i => g i (π i)).card + min R.card S.card ≤
    (Finset.univ.filter fun i => g i (ρ (π (σ i)))).card + P.card
  have pt : ∀ v, (if g v (π v) then 1 else 0) + (if v ∈ Q' ∪ T then 1 else 0) ≤
      (if g v (ρ (π (σ v))) then 1 else 0) + (if v ∈ P then 1 else 0) := by
    intro v
    by_cases hvQ' : v ∈ Q'
    · have hvQ := (memQ v).1 (hQ'Q hvQ')
      have hσ : π (σ v) = c := ((memP _).1 (hP'P (h2 v hvQ'))).1
      have : ρ (π (σ v)) = c' := by simp [ρ, hσ]
      simp [this, hSa v hvQ.1, hun v hvQ.1, hvQ', (memP v).not.2 (by tauto)]
    · by_cases hvT : v ∈ T
      · have hvT' := (memT v).1 hvT
        have hσ : σ v = v := h3 v (fun h => ((memP v).1 (hP'P h)).2 hvT'.2) hvQ'
        have : ρ (π (σ v)) = c' := by simp [ρ, hσ, hvT'.1]
        simp [this, hSa v hvT'.2, hun v hvT'.2, hvT, (memP v).not.2 (by tauto)]
      · by_cases hvP : v ∈ P
        · simp only [hvP, Finset.mem_union, hvQ', hvT, or_self, if_true, if_false]
          split_ifs <;> omega
        · have hσ : σ v = v := h3 v (fun h => hvP (hP'P h)) hvQ'
          have hπ : π v ≠ c := by
            intro h
            by_cases hs : v ∈ S
            · exact hvT ((memT v).2 ⟨h, hs⟩)
            · exact hvP ((memP v).2 ⟨h, hs⟩)
          have : ρ (π (σ v)) = π v := by simp [ρ, hσ, hπ]
          simp [this, hvQ', hvT, hvP]
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) => pt v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
  have hQT : (Q' ∪ T).card = Q'.card + T.card := by
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    exact ((memQ v).1 (hQ'Q hv1)).2 ((memT v).1 hv2).1
  have hRc : R.card = T.card + P.card := by
    rw [hT, hP]; exact (Finset.card_filter_add_card_filter_not _).symm
  have hSc : S.card = T.card + Q.card := by
    have : T.card = (S.filter fun i => π i = c).card := by
      apply Finset.card_bij (fun v _ => v)
      · intro v hv; have := (memT v).1 hv; simp [this.1, this.2]
      · intro _ _ _ _ h; exact h
      · intro v hv; simp only [Finset.mem_filter] at hv
        exact ⟨v, (memT v).2 ⟨hv.2, hv.1⟩, rfl⟩
    rw [this, hQ]; exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hQT] at hsum
  have : min R.card S.card = T.card + min P.card Q.card := by
    rw [hRc, hSc]; omega
  rw [this]
  omega
