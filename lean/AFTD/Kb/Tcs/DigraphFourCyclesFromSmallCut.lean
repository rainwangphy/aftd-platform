import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_four_cycles_from_small_cut

Topic: graphs   Node: 20f76c8a1e47

Provenance: helper lemma. Adaptation of the strong-connectivity argument in arXiv:1805.02999, Section 3, to the four-cycle minimum-counterexample route for OP-110.

In a loopless digraph of minimum outdegree seven, if B is nonempty and all arcs leaving B end in a set S of at most two vertices, a directed cycle in the in-neighborhood of a vertex outside B and S combines with three directed cycles in B to give four disjoint cycles, provided the displayed outdegree-five theorem holds.
-/

theorem digraph_four_cycles_from_small_cut
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj] (hloop : ∀ v, ¬ D.Adj v v)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin 3 → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j)))
    (B S : Finset α) (hB : B.Nonempty) (hS : S.card ≤ 2)
    (hcut : ∀ b ∈ B, ∀ w, D.Adj b w → w ∈ B ∨ w ∈ S)
    (a : α) (haB : a ∉ B) (haS : a ∉ S)
    (C : Finset α) (hC : digraph_directed_cycle_on D C)
    (hin : ∀ v ∈ C, D.Adj v a) :
    ∃ s : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  have hBdeg : ∀ b ∈ B, 5 ≤ (B.filter fun w => D.Adj b w).card := by
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
  obtain ⟨t, ht, hpair⟩ := hthree B hB hBdeg
  have hdis : ∀ i, Disjoint C (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxB := (ht i).1 hxt
    rcases hcut x hxB a (hin x hx) with h | h
    · exact haB h
    · exact haS h
  let f : Fin 4 → Finset α := Fin.cases C t
  refine ⟨f, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hC
    · exact (ht 0).2
    · exact (ht 1).2
    · exact (ht 2).2
  · intro i j hij
    have h01 := hpair (show (0 : Fin 3) ≠ 1 by decide)
    have h02 := hpair (show (0 : Fin 3) ≠ 2 by decide)
    have h12 := hpair (show (1 : Fin 3) ≠ 2 by decide)
    fin_cases i <;> fin_cases j <;>
      first
      | exact (hij rfl).elim
      | exact hdis 0
      | exact hdis 1
      | exact hdis 2
      | exact (hdis 0).symm
      | exact (hdis 1).symm
      | exact (hdis 2).symm
      | exact h01
      | exact h02
      | exact h12
      | exact h01.symm
      | exact h02.symm
      | exact h12.symm
