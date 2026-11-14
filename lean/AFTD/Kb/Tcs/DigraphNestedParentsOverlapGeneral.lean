import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorOverlapIncidenceIdentity
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# digraph_nested_parents_overlap_general

Topic: graphs   Node: 761a262ca96c

Provenance: helper lemma. General form of common-predecessor incidence counting for the twenty-cut equality route; experiment 26346 checks the arithmetic.

For k transitive low vertices pointing to q, nested common-predecessor counts k+3−t force common-predecessor overlap at least twice choose(k+2,3).
-/

private lemma dnpg_sum_two (k : ℕ) : 2 * (∑ j ∈ Finset.range k, (j+1)) = k*(k+1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; nlinarith [ih]

private lemma dnpg_sum_six (k : ℕ) :
    6 * (∑ j ∈ Finset.range k, (j+1)*(k-j)) = k*(k+1)*(k+2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hlast : (k+1)*(k+1-k) = k+1 := by rw [Nat.add_sub_cancel_left, mul_one]
    rw [hlast]
    have hstep : (∑ j ∈ Finset.range k, (j+1)*(k+1-j))
        = (∑ j ∈ Finset.range k, (j+1)*(k-j)) + ∑ j ∈ Finset.range k, (j+1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hkj : k + 1 - j = (k - j) + 1 := by omega
      rw [hkj, mul_add, mul_one]
    rw [hstep]
    have hT := dnpg_sum_two k
    nlinarith [ih, hT]

private lemma dnpg_arith (k : ℕ) :
    (∑ j ∈ Finset.range k, (j+1)*(k-j)) = Nat.choose (k+2) 3 := by
  have h1 := dnpg_sum_six k
  have h2 : 6 * Nat.choose (k+2) 3 = (k+2)*(k+1)*k := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (k+2) 3
    have hfac : (3:ℕ).factorial = 6 := by decide
    rw [hfac] at h
    rw [← h]
    simp [Nat.descFactorial]
    ring
  rw [show k*(k+1)*(k+2) = (k+2)*(k+1)*k from by ring] at h1
  exact Nat.eq_of_mul_eq_mul_left (by decide) (h1.trans h2.symm)

private lemma dnpg_sum_range_fin (k : ℕ) :
    (∑ j : Fin k, (j.val+1)*(k-j.val)) = Nat.choose (k+2) 3 := by
  rw [Fin.sum_univ_eq_sum_range (fun m => (m+1)*(k-m)) k]
  exact dnpg_arith k

theorem digraph_nested_parents_overlap_general
    (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (k : ℕ)
    (low : Fin k → α) (q : α)
    (hinj : Function.Injective low) (hq : ∀ i, low i ≠ q)
    (htrans : ∀ i j : Fin k, i.val < j.val → D.Adj (low j) (low i))
    (htarget : ∀ i, D.Adj (low i) q)
    (hparents : ∀ t : ℕ, 1 ≤ t → t ≤ k →
      k + 3 - t ≤ (Finset.univ.filter fun p : α => p ≠ q ∧
        (∀ i, p ≠ low i) ∧ D.Adj p q ∧
        ∀ i : Fin k, i.val < t → D.Adj p (low i)).card) :
    2 * Nat.choose (k + 2) 3 ≤
      (∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card := by
  rw [← digraph_common_predecessor_overlap_incidence_identity]
  show 2 * Nat.choose (k+2) 3 ≤ ∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
      ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1)
  let Hp : Fin k → Finset α := fun j => Finset.univ.filter (fun p => p ≠ q ∧ (∀ i, p ≠ low i) ∧ D.Adj p q ∧ ∀ i : Fin k, i.val < j.val + 1 → D.Adj p (low i))
  let Lt : Fin k → Finset α := fun j => (Finset.Ioi j).image low
  let Wf : Fin k → Finset α := fun j => Hp j ∪ Lt j
  let ι : Type := (Fin k) ⊕ (Σ j : Fin k, Fin j.val)
  let blk : ι → Fin k := fun i => match i with | Sum.inl j => j | Sum.inr p => p.1
  let g : ι → Sym2 α := fun i => match i with
    | Sum.inl j => Sym2.mk q (low j)
    | Sum.inr p => Sym2.mk (low (p.2.castLT (Nat.lt_trans p.2.isLt p.1.isLt))) (low p.1)
  have hHp_card : ∀ j, k + 3 - (j.val+1) ≤ (Hp j).card := by
    intro j
    exact hparents (j.val+1) (by omega) (by omega)
  have hLt_card : ∀ j, (Lt j).card = k - 1 - j.val := by
    intro j
    show ((Finset.Ioi j).image low).card = k - 1 - j.val
    rw [Finset.card_image_of_injective _ hinj]
    exact Fin.card_Ioi j
  have hdisj : ∀ j, Disjoint (Hp j) (Lt j) := by
    intro j
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Hp, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Lt, Finset.mem_image, Finset.mem_Ioi] at hb
    obtain ⟨j', _, rfl⟩ := hb
    exact ha.2.1 j' rfl
  have hWf_card : ∀ j, 2*(k - j.val) + 1 ≤ (Wf j).card := by
    intro j
    have hcard : (Wf j).card = (Hp j).card + (Lt j).card := Finset.card_union_of_disjoint (hdisj j)
    rw [hcard, hLt_card j]
    have h3 := hHp_card j
    have := j.isLt
    omega
  have hWf_prop : ∀ j (w : α), w ∈ Wf j → D.Adj w q ∧ (∀ i : Fin k, i.val < j.val+1 → D.Adj w (low i)) := by
    intro j w hw
    change w ∈ Hp j ∪ Lt j at hw
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · simp only [Hp, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨hw.2.2.1, hw.2.2.2⟩
    · simp only [Lt, Finset.mem_image, Finset.mem_Ioi] at hw
      obtain ⟨j', hj', rfl⟩ := hw
      refine ⟨htarget j', ?_⟩
      intro i hi
      exact htrans i j' (by omega)
  have hWf_nonempty : ∀ j, (Wf j).Nonempty := by
    intro j
    apply Finset.card_pos.mp
    have := hWf_card j
    omega
  have hg_inj : Function.Injective g := by
    rintro (j | ⟨j, i⟩) (j' | ⟨j', i'⟩) heq
    · dsimp only [g] at heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hinj h2]
      · exact absurd h1.symm (hq j')
    · dsimp only [g] at heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1.symm (hq _)
      · exact absurd h1.symm (hq j')
    · dsimp only [g] at heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 (hq _)
      · exact absurd h2 (hq j)
    · dsimp only [g] at heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h1v : i.val = i'.val := by
          simpa only [Fin.val_castLT] using congrArg Fin.val (hinj h1)
        have h2v : j = j' := hinj h2
        subst h2v
        rw [Fin.ext h1v]
      · have h1v : i.val = j'.val := by
          simpa only [Fin.val_castLT] using congrArg Fin.val (hinj h1)
        have h2v : j.val = i'.val := by
          simpa only [Fin.val_castLT] using congrArg Fin.val (hinj h2)
        have h3 := i.isLt
        have h4 := i'.isLt
        omega
  have hedge1 : ∀ j : Fin k, g (Sum.inl j) ∈ (digraph_common_predecessor_graph D).edgeFinset := by
    intro j
    dsimp only [g]
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    obtain ⟨w, hw⟩ := hWf_nonempty j
    exact ⟨Ne.symm (hq j), w, (hWf_prop j w hw).1, (hWf_prop j w hw).2 j (by omega)⟩
  have hedge2 : ∀ (j : Fin k) (i : Fin j.val),
      g (Sum.inr ⟨j, i⟩) ∈ (digraph_common_predecessor_graph D).edgeFinset := by
    intro j i
    dsimp only [g]
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    refine ⟨?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val (hinj h)
      rw [Fin.val_castLT] at hv
      have := i.isLt
      omega
    · obtain ⟨w, hw⟩ := hWf_nonempty j
      exact ⟨w, (hWf_prop j w hw).2 _ (by rw [Fin.val_castLT]; omega),
        (hWf_prop j w hw).2 j (by omega)⟩
  have hEfam_sub : (Finset.univ.image g) ⊆ (digraph_common_predecessor_graph D).edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨i, _, rfl⟩ := he
    rcases i with j | ⟨j, i⟩
    · exact hedge1 j
    · exact hedge2 j i
  have hbound : ∀ i : ι, 2*(k - (blk i).val) ≤
      (Finset.univ.filter (fun p => ∀ x, x ∈ g i → D.Adj p x)).card - 1 := by
    rintro (j | ⟨j, i⟩)
    · have hsub : Wf j ⊆ Finset.univ.filter (fun p => ∀ x, x ∈ g (Sum.inl j) → D.Adj p x) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [g]
        intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact (hWf_prop j w hw).1
        · exact (hWf_prop j w hw).2 j (by omega)
      have h1 : (Wf j).card ≤ (Finset.univ.filter (fun p => ∀ x, x ∈ g (Sum.inl j) → D.Adj p x)).card :=
        Finset.card_le_card hsub
      have h2 := hWf_card j
      dsimp only [blk]
      omega
    · have hsub : Wf j ⊆ Finset.univ.filter (fun p => ∀ x, x ∈ g (Sum.inr ⟨j, i⟩) → D.Adj p x) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [g]
        intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact (hWf_prop j w hw).2 _ (by rw [Fin.val_castLT]; omega)
        · exact (hWf_prop j w hw).2 j (by omega)
      have h1 : (Wf j).card ≤ (Finset.univ.filter (fun p => ∀ x, x ∈ g (Sum.inr ⟨j, i⟩) → D.Adj p x)).card :=
        Finset.card_le_card hsub
      have h2 := hWf_card j
      dsimp only [blk]
      omega
  have hval : (∑ i : ι, 2*(k - (blk i).val)) = 2 * ∑ j : Fin k, (j.val+1)*(k-j.val) := by
    dsimp only [ι, blk]
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [Nat.cast_id]
    ring
  calc 2 * Nat.choose (k+2) 3
      = 2 * ∑ j : Fin k, (j.val+1)*(k-j.val) := by rw [dnpg_sum_range_fin]
    _ = ∑ i : ι, 2*(k - (blk i).val) := hval.symm
    _ ≤ ∑ i : ι, ((Finset.univ.filter (fun p => ∀ x, x ∈ g i → D.Adj p x)).card - 1) :=
        Finset.sum_le_sum (fun i _ => hbound i)
    _ = ∑ e ∈ Finset.univ.image g, ((Finset.univ.filter (fun p => ∀ x, x ∈ e → D.Adj p x)).card - 1) := by
        rw [Finset.sum_image (s := Finset.univ) (g := g)
          (f := fun e => ((Finset.univ.filter (fun p => ∀ x, x ∈ e → D.Adj p x)).card - 1)) hg_inj.injOn]
    _ ≤ ∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
          ((Finset.univ.filter (fun p => ∀ x, x ∈ e → D.Adj p x)).card - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hEfam_sub (fun i _ _ => Nat.zero_le _)
