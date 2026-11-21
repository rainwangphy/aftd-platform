import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet
import AFTD.Kb.GameTheoryEconomics.CanForce
import AFTD.Kb.GameTheoryEconomics.HasTypeWManipulation

/-!
# pairwise_forcing_three_partition_type_w

Topic: social_choice   Node: d712b09b0aa2

Provenance: formalization of a published result. Source: arXiv:2611.26224, Proposition 3

Let A be a set of alternatives and N a finite set of voters partitioned into three nonempty pairwise disjoint subsets C1, C2, C3. If every pairwise union of two of these subsets can force each of three distinct alternatives a, b, c under voting rule f, then there exist a nonempty coalition C and profiles P, P_dev such that C has an obvious group manipulation of type (W) at P by reporting P_dev.
-/

private noncomputable def pairwise_forcing_three_partition_type_w_rank_abc {A : Type*} (a b c : A) (x : A) : Fin 4 := by
  classical
  exact if x = a then (3 : Fin 4) else if x = b then 2 else if x = c then 1 else 0

private noncomputable def pairwise_forcing_three_partition_type_w_rank_bca {A : Type*} (a b c : A) (x : A) : Fin 4 := by
  classical
  exact if x = b then (3 : Fin 4) else if x = c then 2 else if x = a then 1 else 0

private noncomputable def pairwise_forcing_three_partition_type_w_rank_cab {A : Type*} (a b c : A) (x : A) : Fin 4 := by
  classical
  exact if x = c then (3 : Fin 4) else if x = a then 2 else if x = b then 1 else 0

private noncomputable def pairwise_forcing_three_partition_type_w_order_from_rank {A : Type*} (base : LinearOrder A) (r : A → Fin 4) : LinearOrder A :=
  letI : LinearOrder A := base
  LinearOrder.lift' (fun x : A => toLex (r x, x)) (by
    intro x y h
    have h2 : (ofLex (toLex (r x, x)) : Fin 4 × A).2 = (ofLex (toLex (r y, y)) : Fin 4 × A).2 := by
      simpa using congrArg (fun z => (ofLex z : Fin 4 × A).2) h
    simpa using h2)

private lemma pairwise_forcing_three_partition_type_w_order_from_rank_lt {A : Type*} (base : LinearOrder A) (r : A → Fin 4) (x y : A) :
    @LT.lt A (pairwise_forcing_three_partition_type_w_order_from_rank base r).toLT x y ↔
      Prod.Lex (· < ·) (· < ·) (r x, x) (r y, y) := by
  rfl

private lemma pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt {A : Type*} {base : LinearOrder A}
    {r : A → Fin 4} {x y : A} (h : r x < r y) :
    @LT.lt A (pairwise_forcing_three_partition_type_w_order_from_rank base r).toLT x y := by
  rw [pairwise_forcing_three_partition_type_w_order_from_rank_lt, Prod.lex_def]
  exact Or.inl h

private lemma pairwise_forcing_three_partition_type_w_has_type_w_manipulation_of_can_force {N A : Type*}
    (f : (N → LinearOrder A) → A) (C : Finset N) (P : N → LinearOrder A) (x v : A)
    (hv : v ∈ voting_option_set f C P)
    (hforce : can_force f C x)
    (hpref : ∀ i ∈ C, @LT.lt A (P i).toLT v x) :
    ∃ P_dev, has_type_w_manipulation f C P P_dev := by
  rcases hforce with ⟨P', hP'⟩
  refine ⟨P', ?_⟩
  dsimp [has_type_w_manipulation]
  refine ⟨v, hv, ?_⟩
  intro y hy i hi
  have hyx : y = x := by
    have : y ∈ ({x} : Set A) := by
      rw [← hP']
      exact hy
    simpa using this
  subst y
  exact hpref i hi

/-- Proposition 3 of arXiv:2611.26224: A voting rule admits an obvious group manipulation of type (W) if the voter set can be partitioned into three nonempty blocks whose pairwise unions each force three distinct alternatives. -/
theorem pairwise_forcing_three_partition_type_w
    {N A : Type*} [Fintype N] [DecidableEq N]
    (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (C1 C2 C3 : Finset N)
    (h1 : C1.Nonempty) (h2 : C2.Nonempty) (h3 : C3.Nonempty)
    (hd12 : Disjoint C1 C2) (hd23 : Disjoint C2 C3) (hd13 : Disjoint C1 C3)
    (hu : C1 ∪ C2 ∪ C3 = Finset.univ)
    (f : (N → LinearOrder A) → A)
    (hf12 : ∀ x ∈ ({a, b, c} : Set A), can_force f (C1 ∪ C2) x)
    (hf23 : ∀ x ∈ ({a, b, c} : Set A), can_force f (C2 ∪ C3) x)
    (hf13 : ∀ x ∈ ({a, b, c} : Set A), can_force f (C1 ∪ C3) x) :
    ∃ (C : Finset N), C.Nonempty ∧ ∃ (P P_dev : N → LinearOrder A),
      has_type_w_manipulation f C P P_dev := by
  classical
  let base : LinearOrder A := IsWellOrder.linearOrder (WellOrderingRel (α := A))
  let p1 : LinearOrder A := pairwise_forcing_three_partition_type_w_order_from_rank base (pairwise_forcing_three_partition_type_w_rank_abc a b c)
  let p2 : LinearOrder A := pairwise_forcing_three_partition_type_w_order_from_rank base (pairwise_forcing_three_partition_type_w_rank_bca a b c)
  let p3 : LinearOrder A := pairwise_forcing_three_partition_type_w_order_from_rank base (pairwise_forcing_three_partition_type_w_rank_cab a b c)
  let P : N → LinearOrder A := fun i => if i ∈ C1 then p1 else if i ∈ C2 then p2 else p3
  let v : A := f P
  have hP1 : ∀ i, i ∈ C1 → P i = p1 := by
    intro i hi
    simp [P, hi]
  have hP2 : ∀ i, i ∈ C2 → P i = p2 := by
    intro i hi
    have hi1 : i ∉ C1 := (Finset.disjoint_right.mp hd12) hi
    simp [P, hi1, hi]
  have hP3 : ∀ i, i ∈ C3 → P i = p3 := by
    intro i hi
    have hi1 : i ∉ C1 := (Finset.disjoint_right.mp hd13) hi
    have hi2 : i ∉ C2 := (Finset.disjoint_right.mp hd23) hi
    simp [P, hi1, hi2]
  have hmem : ∀ C : Finset N, v ∈ voting_option_set f C P := by
    intro C
    dsimp [v, voting_option_set]
    exact ⟨P, by intro i hi; rfl, rfl⟩
  have hn12 : (C1 ∪ C2).Nonempty := Finset.union_nonempty.mpr (Or.inl h1)
  have hn23 : (C2 ∪ C3).Nonempty := Finset.union_nonempty.mpr (Or.inl h2)
  have hn13 : (C1 ∪ C3).Nonempty := Finset.union_nonempty.mpr (Or.inl h1)
  have hf12a : can_force f (C1 ∪ C2) a := hf12 a (by simp)
  have hf12b : can_force f (C1 ∪ C2) b := hf12 b (by simp)
  have hf23c : can_force f (C2 ∪ C3) c := hf23 c (by simp)
  have hf13a : can_force f (C1 ∪ C3) a := hf13 a (by simp)
  by_cases hva : v = a
  · have hpref : ∀ i ∈ C2 ∪ C3, @LT.lt A (P i).toLT v c := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi2 | hi3
      · rw [hP2 i hi2, hva]
        exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_bca, hab, hbc.symm, hac])
      · rw [hP3 i hi3, hva]
        exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_cab, hac])
    obtain ⟨Pdev, hdev⟩ := pairwise_forcing_three_partition_type_w_has_type_w_manipulation_of_can_force f (C2 ∪ C3) P c v (hmem _) hf23c hpref
    exact ⟨C2 ∪ C3, hn23, P, Pdev, hdev⟩
  · by_cases hvb : v = b
    · have hpref : ∀ i ∈ C1 ∪ C3, @LT.lt A (P i).toLT v a := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi1 | hi3
        · rw [hP1 i hi1, hvb]
          exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_abc, hab.symm])
        · rw [hP3 i hi3, hvb]
          exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_cab, hab.symm, hbc, hac])
      obtain ⟨Pdev, hdev⟩ := pairwise_forcing_three_partition_type_w_has_type_w_manipulation_of_can_force f (C1 ∪ C3) P a v (hmem _) hf13a hpref
      exact ⟨C1 ∪ C3, hn13, P, Pdev, hdev⟩
    · by_cases hvc : v = c
      · have hpref : ∀ i ∈ C1 ∪ C2, @LT.lt A (P i).toLT v b := by
          intro i hi
          rcases Finset.mem_union.mp hi with hi1 | hi2
          · rw [hP1 i hi1, hvc]
            exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_abc, hab.symm, hbc.symm, hac.symm])
          · rw [hP2 i hi2, hvc]
            exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_bca, hbc.symm])
        obtain ⟨Pdev, hdev⟩ := pairwise_forcing_three_partition_type_w_has_type_w_manipulation_of_can_force f (C1 ∪ C2) P b v (hmem _) hf12b hpref
        exact ⟨C1 ∪ C2, hn12, P, Pdev, hdev⟩
      · have hpref : ∀ i ∈ C1 ∪ C2, @LT.lt A (P i).toLT v a := by
          intro i hi
          rcases Finset.mem_union.mp hi with hi1 | hi2
          · rw [hP1 i hi1]
            exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_abc, hva, hvb, hvc])
          · rw [hP2 i hi2]
            exact pairwise_forcing_three_partition_type_w_order_from_rank_lt_of_rank_lt (by simp [pairwise_forcing_three_partition_type_w_rank_bca, hab, hac, hva, hvb, hvc])
        obtain ⟨Pdev, hdev⟩ := pairwise_forcing_three_partition_type_w_has_type_w_manipulation_of_can_force f (C1 ∪ C2) P a v (hmem _) hf12a hpref
        exact ⟨C1 ∪ C2, hn12, P, Pdev, hdev⟩
