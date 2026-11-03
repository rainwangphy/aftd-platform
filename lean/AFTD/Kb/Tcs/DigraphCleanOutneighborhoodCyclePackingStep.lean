import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_clean_outneighborhood_cycle_packing_step

Topic: graphs   Node: f4045713ecfe

Provenance: helper lemma. General linear out-neighborhood deletion step for OP-110 and the corresponding k-cycle problem.

A directed cycle inside a clean out-neighborhood can be added to any k-cycle packing theorem two outdegree units lower.
-/

theorem digraph_clean_outneighborhood_cycle_packing_step
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (k d : ℕ)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdeg : ∀ v, d + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hpack : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, d ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin k → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j)))
    (v : α) (C : Finset α) (hC : digraph_directed_cycle_on D C)
    (hCout : ∀ w ∈ C, D.Adj v w)
    (hclean : ∀ a b, a ≠ b → D.Adj v a → D.Adj v b →
      ∀ x, D.Adj x a → D.Adj x b → x = v)
    (p : α) (hpv : D.Adj p v) :
    ∃ s : Fin (k + 1) → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  classical
  let T : Finset α := (Finset.univ.erase v) \ C
  have hpne : p ≠ v := by intro h; subst p; exact hloop v hpv
  have hpC : p ∉ C := by
    intro hp
    exact (hori p v hpv) (hCout p hp)
  have hT : T.Nonempty := by
    refine ⟨p, ?_⟩
    simp [T, hpne, hpC]
  have hTdeg : ∀ x ∈ T, d ≤ (T.filter fun w => D.Adj x w).card := by
    intro x hx
    have hxne : x ≠ v := by
      have := (Finset.mem_sdiff.mp hx).1
      exact (Finset.mem_erase.mp this).1
    let A : Finset α := C.filter fun w => D.Adj x w
    have hA : A.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have haC : a ∈ C := (Finset.mem_filter.mp ha).1
      have hbC : b ∈ C := (Finset.mem_filter.mp hb).1
      have hxa : D.Adj x a := (Finset.mem_filter.mp ha).2
      have hxb : D.Adj x b := (Finset.mem_filter.mp hb).2
      by_contra hab
      exact hxne (hclean a b hab (hCout a haC) (hCout b hbC) x hxa hxb)
    have hs : (Finset.univ.filter fun w => D.Adj x w) ⊆
        (T.filter fun w => D.Adj x w) ∪ (A ∪ {v}) := by
      intro w hw
      have hwadj := (Finset.mem_filter.mp hw).2
      by_cases hwv : w = v
      · simp [hwv]
      by_cases hwC : w ∈ C
      · have hwA : w ∈ A := Finset.mem_filter.mpr ⟨hwC, hwadj⟩
        exact Finset.mem_union_right _ (Finset.mem_union_left _ hwA)
      · have hwT : w ∈ T := by simp [T, hwv, hwC]
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwT, hwadj⟩)
    have hsub := Finset.card_le_card hs
    have hunion := Finset.card_union_le (T.filter fun w => D.Adj x w) (A ∪ {v})
    have hsmall := Finset.card_union_le A ({v} : Finset α)
    have hd := hdeg x
    simp only [Finset.card_singleton] at hsmall
    omega
  obtain ⟨t, ht, hpair⟩ := hpack T hT hTdeg
  have hdis : ∀ i, Disjoint C (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxT := (ht i).1 hxt
    exact (Finset.mem_sdiff.mp hxT).2 hx
  let f : Fin (k + 1) → Finset α := Fin.cases C t
  refine ⟨f, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hC
    · exact (ht i).2
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact (hij rfl).elim
      · intro _
        exact hdis j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact (hdis i).symm
      · intro hij
        exact hpair (by simpa using hij)
