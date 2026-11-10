import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickGameIsSpe
import AFTD.Kb.GameTheoryEconomics.PickGameRootAllocation
import AFTD.Kb.GameTheoryEconomics.BlockSnakeSeqTwo
import AFTD.Kb.GameTheoryEconomics.IsNelPd
import AFTD.Kb.GameTheoryEconomics.IsEf1Pd
import AFTD.Kb.GameTheoryEconomics.PickGameMoveZero
import AFTD.Kb.GameTheoryEconomics.PickGameMovePayoff

/-!
# block_snake_two_agent_spe_nel_ef1_three_items

Topic: fair_division   Node: 188353abfbd7

Provenance: helper lemma. Three-item special case of OP-1323; arXiv:2611.09685, Section 7.

For two agents with positive additive values that are distinct across three items for each agent, every subgame-perfect continuation profile of the two-agent block-snake picking game has a root allocation satisfying both NEL and EF1 in pairwise dominance for the item rankings induced by those values.
-/

theorem block_snake_two_agent_spe_nel_ef1_three_items (u : Fin 2 → Fin 3 → ℝ)
    (hu : ∀ i x, 0 < u i x)
    (hd : ∀ i x y, x ≠ y → u i x ≠ u i y)
    (F : List (Fin 3) → Finset (Fin 3))
    (hF : pick_game_is_spe u (block_snake_seq_two 1) F) :
    is_nel_pd (fun i x y => u i x ≤ u i y) (pick_game_root_allocation F) ∧
    is_ef1_pd (fun i x y => u i x ≤ u i y) (pick_game_root_allocation F) := by
  obtain ⟨hlen, hspec⟩ := hF
  have hs0 : (block_snake_seq_two 1).getD 0 0 = 0 := by decide
  have hs1 : (block_snake_seq_two 1).getD 1 0 = 1 := by decide
  have hs2 : (block_snake_seq_two 1).getD 2 0 = 1 := by decide
  have hpair : ∀ a b : Fin 3, a ≠ b → F [a, b] = ∅ := by
    intro a b hab
    have hh : ([a, b] : List (Fin 3)).Nodup := by simp [hab]
    have hy := hspec [a, b] hh
    simp only [List.toFinset_cons, List.toFinset_nil] at hy
    obtain ⟨-, hif⟩ := hy
    have hne : (Finset.univ \ (insert a (insert b ∅)) : Finset (Fin 3)).Nonempty := by
      rw [← Finset.card_pos]
      rw [Finset.card_sdiff_of_subset (by simp [Finset.subset_iff])]
      simp [hab]
    rw [if_pos hne] at hif
    obtain ⟨c, hc, hFc, -⟩ := hif
    simp only [pick_game_move_zero, List.length_cons, List.length_nil, hs2] at hFc
    have hc3 : ([a, b] ++ [c] : List (Fin 3)) = [a, b, c] := rfl
    rw [hc3] at hFc
    have hcad : a ≠ c := fun h => (Finset.mem_sdiff.mp hc).2 (by simp [h])
    have hcbd : b ≠ c := fun h => (Finset.mem_sdiff.mp hc).2 (by simp [h])
    have hnodup3 : ([a, b, c] : List (Fin 3)).Nodup := by simp [hab, hcad, hcbd]
    have hz := hspec [a, b, c] hnodup3
    simp only [List.toFinset_cons, List.toFinset_nil] at hz
    obtain ⟨-, hif3⟩ := hz
    have hempty : (Finset.univ \ (insert a (insert b (insert c ∅))) : Finset (Fin 3)) = ∅ := by
      have hcard : (insert a (insert b (insert c ∅)) : Finset (Fin 3)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
        · simp
        · simp [hcbd]
        · simp [hab, hcad]
      have huniv : (insert a (insert b (insert c ∅)) : Finset (Fin 3)) = Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa using hcard
      rw [huniv, Finset.sdiff_self]
    rw [hempty] at hif3
    rw [if_neg Finset.not_nonempty_empty] at hif3
    rw [hif3] at hFc
    exact hFc
  have hsing : ∀ y : Fin 3, F [y] = ∅ := by
    intro y
    have hy := hspec [y] (by simp)
    simp only [List.toFinset_cons, List.toFinset_nil] at hy
    obtain ⟨-, hif⟩ := hy
    have hne : (Finset.univ \ (insert y ∅) : Finset (Fin 3)).Nonempty := by
      rw [← Finset.card_pos]
      rw [Finset.card_sdiff_of_subset (by simp [Finset.subset_iff])]
      simp
    rw [if_pos hne] at hif
    obtain ⟨c, hc, hFc, -⟩ := hif
    simp only [pick_game_move_zero, List.length_cons, List.length_nil, hs1] at hFc
    have hc1 : ([y] ++ [c] : List (Fin 3)) = [y, c] := rfl
    rw [hc1] at hFc
    have hyc : y ≠ c := fun h => (Finset.mem_sdiff.mp hc).2 (by simp [h])
    rw [hpair y c hyc] at hFc
    exact hFc
  have hroot := hspec [] List.nodup_nil
  simp only [List.toFinset_nil, Finset.sdiff_empty] at hroot
  obtain ⟨-, hif0⟩ := hroot
  rw [if_pos Finset.univ_nonempty] at hif0
  obtain ⟨x, -, hFx, hopt⟩ := hif0
  simp only [pick_game_move_zero, List.length_nil, hs0, List.nil_append] at hFx
  have hFroot : F [] = {x} := by
    rw [hFx, hsing x]
    rfl
  have hpay : ∀ z : Fin 3, pick_game_move_payoff u (block_snake_seq_two 1) F [] z = u 0 z := by
    intro z
    simp only [pick_game_move_payoff, pick_game_move_zero, List.length_nil, hs0, hsing z,
      if_true, List.nil_append]
    simp
  have hopt' : ∀ y : Fin 3, u 0 y ≤ u 0 x := by
    intro y
    have h := hopt y (Finset.mem_univ y)
    rw [hpay y, hpay x] at h
    exact h
  have hA0 : pick_game_root_allocation F 0 = {x} := by
    simp [pick_game_root_allocation, hFroot]
  have hA1 : pick_game_root_allocation F 1 = Finset.univ \ {x} := by
    simp [pick_game_root_allocation, hFroot]
  have hc1 : (Finset.univ \ ({x} : Finset (Fin 3))).card = 2 := by
    rw [Finset.card_sdiff_of_subset (by simp [Finset.subset_iff])]
    simp
  have hA0card : (pick_game_root_allocation F 0).card = 1 := by
    rw [hA0]; simp
  have hA1card : (pick_game_root_allocation F 1).card = 2 := by
    rw [hA1]; exact hc1
  have hc1e : ∀ y ∈ (Finset.univ \ ({x} : Finset (Fin 3))),
      ((Finset.univ \ ({x} : Finset (Fin 3))).erase y).card ≤ 1 := by
    intro y hy
    have h := Finset.card_erase_add_one hy
    omega
  have key : ∀ (i : Fin 2) (S : Finset (Fin 3)), S.card ≤ 1 →
      (∀ z ∈ S, u i z ≤ u i x) →
      ∃ f : Fin 3 → Fin 3, (∀ z ∈ S, f z ∈ ({x} : Finset (Fin 3))) ∧
        (∀ z₁ ∈ S, ∀ z₂ ∈ S, f z₁ = f z₂ → z₁ = z₂) ∧
        ∀ z ∈ S, u i z ≤ u i (f z) := by
    intro i S hS hpref
    refine ⟨fun _ => x, ?_, ?_, ?_⟩
    · intro z _; simp
    · intro z1 hz1 z2 hz2 _; exact Finset.card_le_one.mp hS z1 hz1 z2 hz2
    · intro z hz; simpa using hpref z hz
  constructor
  · intro i j hij y hy
    have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hi01 with rfl | rfl <;> rcases hj01 with rfl | rfl
    · exact absurd hij (lt_irrefl _)
    · rw [hA1] at hy
      rw [hA0, hA1]
      exact key 0 _ (hc1e y hy) (fun z _ => hopt' z)
    · rw [hA1card, hA0card] at hij
      omega
    · exact absurd hij (lt_irrefl _)
  · intro i j
    have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hi01 with rfl | rfl <;> rcases hj01 with rfl | rfl
    · left
      exact ⟨fun z => z, by intro z hz; exact hz,
        by intro z1 _ z2 _ h; exact h,
        by intro z _; exact le_refl _⟩
    · right
      have hne : (Finset.univ \ ({x} : Finset (Fin 3))).Nonempty := by
        rw [← Finset.card_pos, hc1]; norm_num
      obtain ⟨y, hy⟩ := hne
      refine ⟨y, ?_, ?_⟩
      · rw [hA1]; exact hy
      · rw [hA0, hA1]
        exact key 0 _ (hc1e y hy) (fun z _ => hopt' z)
    · right
      refine ⟨x, ?_, ?_⟩
      · rw [hA0]; simp
      · rw [hA0, hA1]
        refine ⟨fun _ => x, ?_, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_erase, Finset.mem_singleton] at hz
          exact absurd hz.2 hz.1
        · intro z1 hz1 z2 hz2 _
          simp only [Finset.mem_erase, Finset.mem_singleton] at hz1
          exact absurd hz1.2 hz1.1
        · intro z hz
          simp only [Finset.mem_erase, Finset.mem_singleton] at hz
          exact absurd hz.2 hz.1
    · left
      exact ⟨fun z => z, by intro z hz; exact hz,
        by intro z1 _ z2 _ h; exact h,
        by intro z _; exact le_refl _⟩
