import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEF1
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1OfCardLeTwoMul
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1PairOfCountLeTwo

/-!
# round_robin_three_agents_seven_goods_pne_ef1

Topic: fair_division   Node: 9f3d96068a82

Provenance: original. Related work: Smallest open case of round_robin_pne_ef1_of_card_le_two_mul_add_one; arXiv:2610.23686 Proposition 1 has eight goods.

With three agents and seven goods, every pure Nash equilibrium of Round-Robin (nonnegative additive valuations) is EF1; so the eight-good counterexample of arXiv:2610.23686 Proposition 1 is the smallest possible.
-/

/-- `g` is the top good of ranking `r` outside `S`. -/
def rr37_top (r : Fin 7 ≃ Fin 7) (S : Finset (Fin 7)) (g : Fin 7) : Prop :=
  g ∉ S ∧ ∀ h, h ∉ S → r.symm g ≤ r.symm h

theorem rr37_turn {N : Type*} [DecidableEq N] (r : Fin 7 ≃ Fin 7) (i : N)
    (A : N → Finset (Fin 7)) (S : Finset (Fin 7)) (g : Fin 7) (hg : rr37_top r S g) :
    picking_turn (List.ofFn r) i (A, S) = (Function.update A i (insert g (A i)), insert g S) := by
  have hf : (List.ofFn r).find? (fun x => decide (x ∉ S)) = some g := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hg.1, (r.symm g).val, by simp, by simp only [List.getElem_ofFn]; simp, ?_⟩
    intro j hj
    have hj' : j < 7 := by have := (r.symm g).isLt; omega
    simp only [List.getElem_ofFn, decide_not, Bool.not_not, decide_eq_true_eq]
    by_contra hc
    have := hg.2 _ hc
    simp only [Equiv.symm_apply_apply] at this
    exact absurd this (by rw [Fin.le_def]; simp; omega)
  simp only [picking_turn, hf]

theorem rr37_exists (r : Fin 7 ≃ Fin 7) (S : Finset (Fin 7)) (hS : S.card < 7) :
    ∃ g, rr37_top r S g := by
  have hne : (Finset.univ \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [Finset.sdiff_eq_empty_iff_subset] at he
    have := Finset.card_le_card he
    simp at this
    omega
  obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image _ r.symm hne
  exact ⟨g, by simpa using hg, fun h hh => hmin h (by simpa using hh)⟩

theorem rr37_unique {r : Fin 7 ≃ Fin 7} {S : Finset (Fin 7)} {g g' : Fin 7}
    (h : rr37_top r S g) (h' : rr37_top r S g') : g = g' :=
  r.symm.injective (le_antisymm (h.2 g' h'.1) (h'.2 g h.1))

theorem rr37_first {r : Fin 7 ≃ Fin 7} {S : Finset (Fin 7)} {g : Fin 7}
    (h0 : r 0 = g) (hg : g ∉ S) : rr37_top r S g :=
  ⟨hg, fun h _ => by rw [← h0, Equiv.symm_apply_apply]; exact Fin.zero_le _⟩

theorem rr37_second {r : Fin 7 ≃ Fin 7} {S : Finset (Fin 7)} {g : Fin 7}
    (h0 : r 0 ∈ S) (h1 : r 1 = g) (hg : g ∉ S) : rr37_top r S g := by
  refine ⟨hg, fun h hh => ?_⟩
  rw [← h1, Equiv.symm_apply_apply]
  have : r.symm h ≠ 0 := by
    intro he
    rw [Equiv.symm_apply_eq] at he
    exact hh (he ▸ h0)
  rw [Fin.le_def]
  rw [Ne, Fin.ext_iff] at this
  simp only [Fin.val_zero] at this
  simp only [Fin.val_one]
  omega

theorem rr37_two (a b : Fin 7) (hab : a ≠ b) : ∃ r : Fin 7 ≃ Fin 7, r 0 = a ∧ r 1 = b := by
  refine ⟨(Equiv.swap 1 (Equiv.swap 0 a b)).trans (Equiv.swap 0 a), ?_⟩
  revert a b
  decide

theorem rr37_run (R : Fin 3 → Fin 7 ≃ Fin 7) :
    ∃ g1 g2 g3 g4 g5 g6 g7 : Fin 7,
      rr37_top (R 0) ∅ g1 ∧ rr37_top (R 1) (insert g1 ∅) g2 ∧
      rr37_top (R 2) (insert g2 (insert g1 ∅)) g3 ∧
      rr37_top (R 0) (insert g3 (insert g2 (insert g1 ∅))) g4 ∧
      rr37_top (R 1) (insert g4 (insert g3 (insert g2 (insert g1 ∅)))) g5 ∧
      rr37_top (R 2) (insert g5 (insert g4 (insert g3 (insert g2 (insert g1 ∅))))) g6 ∧
      rr37_top (R 0) (insert g6 (insert g5 (insert g4 (insert g3 (insert g2 (insert g1 ∅)))))) g7 ∧
      picking_sequence_outcome (round_robin_sequence 3 7) R 0 = {g7, g4, g1} ∧
      picking_sequence_outcome (round_robin_sequence 3 7) R 1 = {g5, g2} ∧
      picking_sequence_outcome (round_robin_sequence 3 7) R 2 = {g6, g3} := by
  have hc : ∀ S : Finset (Fin 7), ∀ a, S.card < 6 → (insert a S).card < 7 := fun S a hS =>
    lt_of_le_of_lt (Finset.card_insert_le a S) (by omega)
  obtain ⟨g1, h1⟩ := rr37_exists (R 0) ∅ (by simp)
  obtain ⟨g2, h2⟩ := rr37_exists (R 1) (insert g1 ∅) (by simp)
  obtain ⟨g3, h3⟩ := rr37_exists (R 2) (insert g2 (insert g1 ∅))
    (hc _ _ (lt_of_le_of_lt (Finset.card_insert_le _ _) (by simp)))
  obtain ⟨g4, h4⟩ := rr37_exists (R 0) (insert g3 (insert g2 (insert g1 ∅)))
    (hc _ _ (lt_of_le_of_lt (Finset.card_insert_le _ _)
      (Nat.succ_lt_succ (lt_of_le_of_lt (Finset.card_insert_le _ _) (by simp)))))
  have hc4 : (insert g4 (insert g3 (insert g2 (insert g1 (∅ : Finset (Fin 7)))))).card ≤ 4 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
  obtain ⟨g5, h5⟩ := rr37_exists (R 1) (insert g4 (insert g3 (insert g2 (insert g1 ∅))))
    (by omega)
  obtain ⟨g6, h6⟩ := rr37_exists (R 2) (insert g5 (insert g4 (insert g3 (insert g2 (insert g1 ∅)))))
    (lt_of_le_of_lt (Finset.card_insert_le _ _) (by omega))
  obtain ⟨g7, h7⟩ := rr37_exists (R 0)
    (insert g6 (insert g5 (insert g4 (insert g3 (insert g2 (insert g1 ∅))))))
    (lt_of_le_of_lt (Finset.card_insert_le _ _)
      (Nat.succ_lt_succ (lt_of_le_of_lt (Finset.card_insert_le _ _) (by omega))))
  have hseq : round_robin_sequence 3 7 = [0, 1, 2, 0, 1, 2, 0] := by decide
  refine ⟨g1, g2, g3, g4, g5, g6, g7, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  simp only [picking_sequence_outcome, hseq, List.foldl_cons, List.foldl_nil]
  rw [rr37_turn _ _ _ _ _ h1, rr37_turn _ _ _ _ _ h2, rr37_turn _ _ _ _ _ h3,
    rr37_turn _ _ _ _ _ h4, rr37_turn _ _ _ _ _ h5, rr37_turn _ _ _ _ _ h6,
    rr37_turn _ _ _ _ _ h7]
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem rr37_agent2 (w : Fin 3 → Fin 7 → ℝ) (rank : Fin 3 → Fin 7 ≃ Fin 7)
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence 3 7) rank) :
    ∃ g ∈ picking_sequence_outcome (round_robin_sequence 3 7) rank 0,
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val 2
          (picking_sequence_outcome (round_robin_sequence 3 7) rank 0 \ {g}) ≤
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val 2
          (picking_sequence_outcome (round_robin_sequence 3 7) rank 2) := by
  obtain ⟨x1, y2, z3, x4, y5, z6, x7, a1, a2, a3, a4, a5, a6, a7, hA0, hA1, hA2⟩ := rr37_run rank
  have n2 := a2.1; have n3 := a3.1; have n4 := a4.1; have n5 := a5.1; have n6 := a6.1
  have n7 := a7.1
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false, not_or] at n2 n3 n4 n5 n6 n7
  have e0 : ∀ r, Function.update rank 2 r 0 = rank 0 := fun r => Function.update_of_ne (by decide) _ _
  have e1 : ∀ r, Function.update rank 2 r 1 = rank 1 := fun r => Function.update_of_ne (by decide) _ _
  have e2 : ∀ r, Function.update rank 2 r 2 = r := fun r => Function.update_self _ _ _
  have key : ∀ r, ∑ g ∈ picking_sequence_outcome (round_robin_sequence 3 7)
      (Function.update rank 2 r) 2, w 2 g ≤ w 2 z6 + w 2 z3 := by
    intro r
    have := h 2 r
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation] at this
    rw [hA2, Finset.sum_pair n6.2.2.1] at this
    exact this
  refine ⟨x1, by rw [hA0]; simp, ?_⟩
  have hsd : ({x7, x4, x1} : Finset (Fin 7)) \ {x1} = {x7, x4} := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩ <;> simp_all
    · rintro (h1 | h1) <;> subst h1 <;> simp_all
  rw [hA0, hA2, hsd]
  simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation]
  rw [Finset.sum_pair n7.2.2.1, Finset.sum_pair n6.2.2.1]
  -- deviation: keep `z3`, then take `x7`
  have hz6x7 : w 2 x7 ≤ w 2 z6 := by
    obtain ⟨r, hr0, hr1⟩ := rr37_two z3 x7 (Ne.symm n7.2.2.2.1)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, c1, c2, c3, c4, c5, c6, c7, -, -, hB2⟩ :=
      rr37_run (Function.update rank 2 r)
    rw [e0] at c1 c4 c7; rw [e1] at c2 c5; rw [e2] at c3 c6
    obtain rfl := rr37_unique a1 c1
    obtain rfl := rr37_unique a2 c2
    obtain rfl := rr37_unique (rr37_first hr0 a3.1) c3
    obtain rfl := rr37_unique a4 c4
    obtain rfl := rr37_unique a5 c5
    obtain rfl := rr37_unique (rr37_second (by rw [hr0]; simp) hr1
      (by simp [n7.2.1, n7.2.2.1, n7.2.2.2.1, n7.2.2.2.2])) c6
    have := key r
    rw [hB2, Finset.sum_pair n7.2.2.2.1] at this
    linarith
  by_cases hc : w 2 x4 ≤ w 2 z3
  · linarith
  rw [not_le] at hc
  -- deviation: take `x4`, then `x7`
  obtain ⟨r, hr0, hr1⟩ := rr37_two x4 x7 (Ne.symm n7.2.2.1)
  obtain ⟨b1, b2, b3, p, q, b6, b7, c1, c2, c3, c4, c5, c6, c7, -, -, hB2⟩ :=
    rr37_run (Function.update rank 2 r)
  rw [e0] at c1 c4 c7; rw [e1] at c2 c5; rw [e2] at c3 c6
  obtain rfl := rr37_unique a1 c1
  obtain rfl := rr37_unique a2 c2
  obtain rfl := rr37_unique (rr37_first hr0 (by simp [n4.2.1, n4.2.2])) c3
  by_cases hx7 : x7 ∈ insert q (insert p (insert x4 (insert y2 (insert x1 (∅ : Finset (Fin 7))))))
  swap
  · obtain rfl := rr37_unique (rr37_second (by rw [hr0]; simp) hr1 hx7) c6
    have := key r
    rw [hB2, Finset.sum_pair (n7.2.2.1)] at this
    linarith
  -- deviation: take `x4`, then `z6`
  obtain ⟨r', hr0', hr1'⟩ := rr37_two x4 z6 (Ne.symm n6.2.1)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, f1, f2, f3, f4, f5, f6, f7, -, -, hD2⟩ :=
    rr37_run (Function.update rank 2 r')
  rw [e0] at f1 f4 f7; rw [e1] at f2 f5; rw [e2] at f3 f6
  obtain rfl := rr37_unique a1 f1
  obtain rfl := rr37_unique a2 f2
  obtain rfl := rr37_unique (rr37_first hr0' (by simp [n4.2.1, n4.2.2])) f3
  obtain rfl := rr37_unique c4 f4
  obtain rfl := rr37_unique c5 f5
  by_cases hz6 : z6 ∈ insert q (insert p (insert x4 (insert y2 (insert x1 (∅ : Finset (Fin 7))))))
  swap
  · obtain rfl := rr37_unique (rr37_second (by rw [hr0']; simp) hr1' hz6) f6
    have := key r'
    rw [hD2, Finset.sum_pair n6.2.1] at this
    linarith
  -- both `x7` and `z6` went to agents 0 and 1, against agent 1's preference for `y5`
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx7 hz6
  have hx7' : x7 = q ∨ x7 = p := by
    rcases hx7 with h | h | h | h | h
    exacts [Or.inl h, Or.inr h, absurd h n7.2.2.1, absurd h n7.2.2.2.2.1, absurd h n7.2.2.2.2.2]
  have hz6' : z6 = q ∨ z6 = p := by
    rcases hz6 with h | h | h | h | h
    exacts [Or.inl h, Or.inr h, absurd h n6.2.1, absurd h n6.2.2.2.1, absurd h n6.2.2.2.2]
  have hpq : (p = x7 ∧ q = z6) ∨ (p = z6 ∧ q = x7) := by
    rcases hx7' with h7 | h7 <;> rcases hz6' with h6 | h6
    · exact absurd (h7.trans h6.symm) n7.1
    · exact Or.inr ⟨h6.symm, h7.symm⟩
    · exact Or.inl ⟨h7.symm, h6.symm⟩
    · exact absurd (h7.trans h6.symm) n7.1
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq] at c5
  · exact absurd ((rank 1).symm.injective (le_antisymm
      (c5.2 y5 (by simp [Ne.symm n7.2.1, n5.1, n5.2.2.1, n5.2.2.2]))
      (a5.2 z6 (by simp [n6.2.1, n6.2.2.1, n6.2.2.2.1, n6.2.2.2.2])))) n6.1
  · exact absurd ((rank 1).symm.injective (le_antisymm
      (c5.2 y5 (by simp [Ne.symm n6.1, n5.1, n5.2.2.1, n5.2.2.2]))
      (a5.2 x7 (by simp [n7.2.2.1, n7.2.2.2.1, n7.2.2.2.2.1, n7.2.2.2.2.2])))) n7.2.1

theorem rr37_agent1 (w : Fin 3 → Fin 7 → ℝ) (rank : Fin 3 → Fin 7 ≃ Fin 7)
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence 3 7) rank) :
    ∃ g ∈ picking_sequence_outcome (round_robin_sequence 3 7) rank 0,
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val 1
          (picking_sequence_outcome (round_robin_sequence 3 7) rank 0 \ {g}) ≤
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val 1
          (picking_sequence_outcome (round_robin_sequence 3 7) rank 1) := by
  obtain ⟨x1, y2, z3, x4, y5, z6, x7, a1, a2, a3, a4, a5, a6, a7, hA0, hA1, hA2⟩ := rr37_run rank
  have n2 := a2.1; have n3 := a3.1; have n4 := a4.1; have n5 := a5.1; have n6 := a6.1
  have n7 := a7.1
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false, not_or] at n2 n3 n4 n5 n6 n7
  have e0 : ∀ r, Function.update rank 1 r 0 = rank 0 := fun r => Function.update_of_ne (by decide) _ _
  have e1 : ∀ r, Function.update rank 1 r 1 = r := fun r => Function.update_self _ _ _
  have e2 : ∀ r, Function.update rank 1 r 2 = rank 2 := fun r => Function.update_of_ne (by decide) _ _
  have key : ∀ r, ∑ g ∈ picking_sequence_outcome (round_robin_sequence 3 7)
      (Function.update rank 1 r) 1, w 1 g ≤ w 1 y5 + w 1 y2 := by
    intro r
    have := h 1 r
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation] at this
    rw [hA1, Finset.sum_pair n5.2.2.1] at this
    exact this
  refine ⟨x1, by rw [hA0]; simp, ?_⟩
  have hsd : ({x7, x4, x1} : Finset (Fin 7)) \ {x1} = {x7, x4} := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩ <;> simp_all
    · rintro (h1 | h1) <;> subst h1 <;> simp_all
  rw [hA0, hA1, hsd]
  simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation]
  rw [Finset.sum_pair n7.2.2.1, Finset.sum_pair n5.2.2.1]
  -- deviation: keep `y2`, then take `x7`
  have hy5x7 : w 1 x7 ≤ w 1 y5 := by
    obtain ⟨r, hr0, hr1⟩ := rr37_two y2 x7 (Ne.symm n7.2.2.2.2.1)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, c1, c2, c3, c4, c5, c6, c7, -, hB1, -⟩ :=
      rr37_run (Function.update rank 1 r)
    rw [e0] at c1 c4 c7; rw [e1] at c2 c5; rw [e2] at c3 c6
    obtain rfl := rr37_unique a1 c1
    obtain rfl := rr37_unique (rr37_first hr0 a2.1) c2
    obtain rfl := rr37_unique a3 c3
    obtain rfl := rr37_unique a4 c4
    obtain rfl := rr37_unique (rr37_second (by rw [hr0]; simp) hr1
      (by simp [n7.2.2.1, n7.2.2.2.1, n7.2.2.2.2.1, n7.2.2.2.2.2])) c5
    have := key r
    rw [hB1, Finset.sum_pair n7.2.2.2.2.1] at this
    linarith
  by_cases hc : w 1 x4 ≤ w 1 y2
  · linarith
  rw [not_le] at hc
  -- deviation: take `x4`, then `x7`
  obtain ⟨r, hr0, hr1⟩ := rr37_two x4 x7 (Ne.symm n7.2.2.1)
  obtain ⟨b1, b2, a, b, b5, b6, b7, c1, c2, c3, c4, c5, c6, c7, -, hB1, -⟩ :=
    rr37_run (Function.update rank 1 r)
  rw [e0] at c1 c4 c7; rw [e1] at c2 c5; rw [e2] at c3 c6
  obtain rfl := rr37_unique a1 c1
  obtain rfl := rr37_unique (rr37_first hr0 (by simp [n4.2.2])) c2
  by_cases hx7 : x7 ∈ insert b (insert a (insert x4 (insert x1 (∅ : Finset (Fin 7)))))
  swap
  · obtain rfl := rr37_unique (rr37_second (by rw [hr0]; simp) hr1 hx7) c5
    have := key r
    rw [hB1, Finset.sum_pair n7.2.2.1] at this
    linarith
  -- deviation: take `x4`, then `y5`
  obtain ⟨r', hr0', hr1'⟩ := rr37_two x4 y5 (Ne.symm n5.1)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, f1, f2, f3, f4, f5, f6, f7, -, hD1, -⟩ :=
    rr37_run (Function.update rank 1 r')
  rw [e0] at f1 f4 f7; rw [e1] at f2 f5; rw [e2] at f3 f6
  obtain rfl := rr37_unique a1 f1
  obtain rfl := rr37_unique (rr37_first hr0' (by simp [n4.2.2])) f2
  obtain rfl := rr37_unique c3 f3
  obtain rfl := rr37_unique c4 f4
  by_cases hy5 : y5 ∈ insert b (insert a (insert x4 (insert x1 (∅ : Finset (Fin 7)))))
  swap
  · obtain rfl := rr37_unique (rr37_second (by rw [hr0']; simp) hr1' hy5) f5
    have := key r'
    rw [hD1, Finset.sum_pair n5.1] at this
    linarith
  -- both `x7` and `y5` went to agents 2 and 0, against agent 2's preference for `z3`
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx7 hy5
  have hx7' : x7 = b ∨ x7 = a := by
    rcases hx7 with h | h | h | h
    exacts [Or.inl h, Or.inr h, absurd h n7.2.2.1, absurd h n7.2.2.2.2.2]
  have hy5' : y5 = b ∨ y5 = a := by
    rcases hy5 with h | h | h | h
    exacts [Or.inl h, Or.inr h, absurd h n5.1, absurd h n5.2.2.2]
  have hab : a = x7 ∨ a = y5 := by
    rcases hx7' with h7 | h7
    · rcases hy5' with h5 | h5
      · exact absurd (h7.trans h5.symm) n7.2.1
      · exact Or.inr h5.symm
    · exact Or.inl h7.symm
  rcases hab with ha | ha <;> rw [ha] at c3
  · exact absurd ((rank 2).symm.injective (le_antisymm
      (c3.2 z3 (by simp [Ne.symm n4.1, n3.2]))
      (a3.2 x7 (by simp [n7.2.2.2.2.1, n7.2.2.2.2.2])))) n7.2.2.2.1
  · exact absurd ((rank 2).symm.injective (le_antisymm
      (c3.2 z3 (by simp [Ne.symm n4.1, n3.2]))
      (a3.2 y5 (by simp [n5.2.2.1, n5.2.2.2])))) n5.2.1

theorem round_robin_three_agents_seven_goods_pne_ef1
    (w : Fin 3 → Fin 7 → ℝ) (hw : ∀ i g, 0 ≤ w i g) (rank : Fin 3 → Fin 7 ≃ Fin 7)
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence 3 7) rank) :
    SocialChoice.FairDivision.Indivisible.IsEF1
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (picking_sequence_outcome (round_robin_sequence 3 7) rank) := by
  intro i j hij hne
  by_cases hj : j = 0
  · subst hj
    fin_cases i
    · exact absurd rfl hij
    · exact rr37_agent1 w rank h
    · exact rr37_agent2 w rank h
  · refine round_robin_pne_ef1_pair_of_count_le_two 3 7 w hw rank h i j hij ?_ hne
    fin_cases j
    · exact absurd rfl hj
    · decide
    · decide
