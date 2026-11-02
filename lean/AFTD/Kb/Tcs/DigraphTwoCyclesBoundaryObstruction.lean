import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphFourCyclesFromTwoCyclesFewBad

/-!
# digraph_two_cycles_boundary_obstruction

Topic: graphs   Node: ca779326e28b

Provenance: helper lemma. General cycle-pair deletion reduction for OP-110; the robust two-cycle hypothesis is a published theorem.

If a digraph of minimum outdegree seven has no four disjoint cycles, then for any two disjoint cycles with nonempty remainder either some outside vertex has at least six out-neighbors in their union or at least three outside vertices have at least five, assuming the displayed robust two-cycle condition.
-/

theorem digraph_two_cycles_boundary_obstruction
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj] (hloop : ∀ v, ¬ D.Adj v v)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card = 2).card ≤ 2 →
      ∃ s : Fin 2 → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j)))
    (C₁ C₂ : Finset α) (hC₁ : digraph_directed_cycle_on D C₁)
    (hC₂ : digraph_directed_cycle_on D C₂) (hdis : Disjoint C₁ C₂)
    (hTne : (Finset.univ \ (C₁ ∪ C₂)).Nonempty)
    (hno : ¬ ∃ s : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∃ v ∉ (C₁ ∪ C₂), 6 ≤ ((C₁ ∪ C₂).filter fun w => D.Adj v w).card) ∨
      3 ≤ ((Finset.univ \ (C₁ ∪ C₂)).filter fun v =>
        5 ≤ ((C₁ ∪ C₂).filter fun w => D.Adj v w).card).card := by
  classical
  by_contra h
  have hnoall : ∀ v ∉ (C₁ ∪ C₂), ((C₁ ∪ C₂).filter fun w => D.Adj v w).card ≤ 5 := by
    intro v hv
    by_contra hh
    apply h
    left
    exact ⟨v, hv, by omega⟩
  have hfew : ((Finset.univ \ (C₁ ∪ C₂)).filter fun v =>
      5 ≤ ((C₁ ∪ C₂).filter fun w => D.Adj v w).card).card ≤ 2 := by
    by_contra hh
    apply h
    right
    omega
  exact hno (digraph_four_cycles_from_two_cycles_few_bad α D hloop hdeg hrobust C₁ C₂ hC₁ hC₂ hdis hTne hnoall hfew)
