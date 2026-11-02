import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_four_cycles_from_undominated_triangle

Topic: graphs   Node: fbe9e7175157

Provenance: helper lemma. Triangle-deletion step toward OP-110 using the outdegree-five three-cycle theorem.

If a finite digraph of minimum outdegree at least seven has a directed triangle that no outside vertex dominates and the displayed three-cycle condition holds on induced subsets, then it has four pairwise vertex-disjoint directed cycles.
-/

theorem digraph_four_cycles_from_undominated_triangle
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin 3 → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j)))
    (C : Finset α) (hC : digraph_directed_cycle_on D C) (hcard : C.card = 3)
    (hnotdom : ∀ v ∉ C, (C.filter fun w => D.Adj v w).card ≤ 2) :
    ∃ s : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  let T := Finset.univ \ C
  have hT : T.Nonempty := by
    by_contra hn
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs : (Finset.univ : Finset α) ⊆ C := by
      intro x hx
      by_cases hxc : x ∈ C
      · exact hxc
      have hxT : x ∈ T := by simp [T, hxc]
      rw [he] at hxT
      simp at hxT
    have hc := Finset.card_le_card hs
    obtain ⟨a⟩ := ‹Nonempty α›
    have hd := hdeg a
    have hdu := Finset.card_le_card (Finset.filter_subset (fun w => D.Adj a w) Finset.univ)
    omega
  have hTdeg : ∀ x ∈ T, 5 ≤ (T.filter fun w => D.Adj x w).card := by
    intro x hx
    have hxc : x ∉ C := by simpa [T] using hx
    have h2 := hnotdom x hxc
    have hs : (Finset.univ.filter fun w => D.Adj x w) ⊆
        (T.filter fun w => D.Adj x w) ∪ (C.filter fun w => D.Adj x w) := by
      intro w hw
      have hadj := (Finset.mem_filter.mp hw).2
      by_cases hwc : w ∈ C
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwc, hadj⟩)
      · have hwT : w ∈ T := by simp [T, hwc]
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwT, hadj⟩)
    have hc := Finset.card_le_card hs
    have hu := Finset.card_union_le (T.filter fun w => D.Adj x w) (C.filter fun w => D.Adj x w)
    have hd := hdeg x
    omega
  obtain ⟨t, ht, hpair⟩ := hthree T hT hTdeg
  have hdis : ∀ i, Disjoint C (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxT := (ht i).1 hxt
    have hxc : x ∉ C := by simpa [T] using hxT
    exact hxc hx
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
