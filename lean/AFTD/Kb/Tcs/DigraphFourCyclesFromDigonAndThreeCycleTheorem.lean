import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_four_cycles_from_digon_and_three_cycle_theorem

Topic: graphs   Node: 581dab5ca60f

Provenance: helper lemma. Digon reduction in the minimum-counterexample route for OP-110, using the published outdegree-five theorem for three cycles.

If a finite loopless digraph has minimum outdegree seven, contains a directed two-cycle, and every nonempty vertex subset whose induced minimum outdegree is five contains three disjoint directed cycles, then it contains four disjoint directed cycles.
-/

theorem digraph_four_cycles_from_digon_and_three_cycle_theorem
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj] (hloop : ∀ v, ¬ D.Adj v v)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin 3 → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j)))
    (u v : α) (huv : D.Adj u v) (hvu : D.Adj v u) :
    ∃ s : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  have huvne : u ≠ v := by intro h; subst v; exact hloop u huv
  let T : Finset α := (Finset.univ.erase u).erase v
  have hcard : 7 ≤ (Finset.univ : Finset α).card :=
    (hdeg u).trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hT : T.Nonempty := by
    by_contra hn
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs : (Finset.univ : Finset α) ⊆ {u,v} := by
      intro x hx
      by_cases hxu : x = u
      · simp [hxu]
      by_cases hxv : x = v
      · simp [hxv]
      have : x ∈ T := by simp [T, hxu, hxv]
      rw [he] at this
      simp at this
    have hh := Finset.card_le_card hs
    have hp : ({u,v} : Finset α).card ≤ 2 := by simp [huvne]
    omega
  have hTdeg : ∀ x ∈ T, 5 ≤ (T.filter fun w => D.Adj x w).card := by
    intro x hx
    have hs : (Finset.univ.filter fun w => D.Adj x w) ⊆
        (T.filter fun w => D.Adj x w) ∪ {u,v} := by
      intro w hw
      have hadj := (Finset.mem_filter.mp hw).2
      by_cases hwu : w = u
      · simp [hwu]
      by_cases hwv : w = v
      · simp [hwv]
      have hwT : w ∈ T := by simp [T, hwu, hwv]
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwT, hadj⟩)
    have hh := Finset.card_le_card hs
    have hu := Finset.card_union_le (T.filter fun w => D.Adj x w) ({u,v} : Finset α)
    have hp : ({u,v} : Finset α).card ≤ 2 := by simp [huvne]
    have hd := hdeg x
    omega
  obtain ⟨t, ht, hpair⟩ := hthree T hT hTdeg
  have h2 : digraph_directed_cycle_on D ({u,v} : Finset α) := by
    refine ⟨[u,v], ?_⟩
    simp [huvne, huv, hvu]
  have hdis : ∀ i, Disjoint ({u,v} : Finset α) (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxT := (ht i).1 hxt
    simp only [T, Finset.mem_erase, Finset.mem_univ, and_true] at hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp_all
  let f : Fin 4 → Finset α := Fin.cases {u,v} t
  refine ⟨f, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h2
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
