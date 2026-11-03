import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_cycle_packing_from_small_directed_cut

Topic: graphs   Node: 26c38e9d660d

Provenance: helper lemma. Generalized directed cut reduction for the minimum-counterexample route to OP-110.

A nonempty directed block with at most two vertices in its outgoing boundary contains s disjoint directed cycles under the stated s-cycle hypothesis; an in-neighborhood cycle of a vertex outside both the block and boundary supplies one more.
-/

theorem digraph_cycle_packing_from_small_directed_cut
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (r s : ℕ) (hdeg : ∀ v, r ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hprev : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, r - 2 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin s → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (B S : Finset α) (hB : B.Nonempty) (hS : S.card ≤ 2)
    (hcut : ∀ b ∈ B, ∀ w, D.Adj b w → w ∈ B ∨ w ∈ S)
    (a : α) (haB : a ∉ B) (haS : a ∉ S)
    (C : Finset α) (hC : digraph_directed_cycle_on D C)
    (hin : ∀ v ∈ C, D.Adj v a) :
    ∃ c : Fin (s + 1) → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)) := by
  have hBdeg : ∀ b ∈ B, r - 2 ≤ (B.filter fun w => D.Adj b w).card := by
    intro b hb
    have hs : (Finset.univ.filter fun w => D.Adj b w) ⊆
        (B.filter fun w => D.Adj b w) ∪ S := by
      intro w hw
      have hadj := (Finset.mem_filter.mp hw).2
      rcases hcut b hb w hadj with hwB | hwS
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwB, hadj⟩)
      · exact Finset.mem_union_right _ hwS
    have hc := Finset.card_le_card hs
    have hu := Finset.card_union_le (B.filter fun w => D.Adj b w) S
    have hd := hdeg b
    omega
  obtain ⟨t, ht, hpair⟩ := hprev B hB hBdeg
  have hdis : ∀ i, Disjoint C (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxB := (ht i).1 hxt
    rcases hcut x hxB a (hin x hx) with h | h
    · exact haB h
    · exact haS h
  let f : Fin (s + 1) → Finset α := Fin.cases C t
  refine ⟨f, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => exact hC
    | succ i' => exact (ht i').2
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j' => exact hdis j'
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact (hdis i').symm
      | succ j' =>
        have hne : i' ≠ j' := by
          intro heq
          subst heq
          exact hij rfl
        exact hpair hne
