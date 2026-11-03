import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphLinearArcDominatedUniqueCommonSuccessor
import AFTD.Kb.Tcs.DigraphCleanOutneighborhoodCyclePackingStep
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphLocalOutneighborhoodCycle

/-!
# digraph_linear_arc_dominated_cycle_packing_step

Topic: graphs   Node: 0bb251f20e70

Provenance: helper lemma. General zero-overlap packing induction for OP-110 and the corresponding k-cycle problem.

The k-cycle theorem at outdegree d implies the (k+1)-cycle theorem at outdegree d+2 for oriented linear arc-dominated digraphs.
-/

theorem digraph_linear_arc_dominated_cycle_packing_step
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj] (k d : ℕ)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdeg : ∀ v, d + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hlinear : ∀ u v, u ≠ v → ∀ a b,
      D.Adj a u → D.Adj a v → D.Adj b u → D.Adj b v → a = b)
    (hpack : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, d ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin k → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ s : Fin (k + 1) → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  classical
  let v : α := Classical.choice ‹Nonempty α›
  have hv : ∃ w, D.Adj v w := by
    have hp : 0 < (Finset.univ.filter fun w => D.Adj v w).card := by
      have := hdeg v
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hp
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩
  have hc : ∀ w, D.Adj v w → ∃ x, D.Adj v x ∧ D.Adj w x := by
    intro w hw
    exact ExistsUnique.exists (digraph_linear_arc_dominated_unique_common_successor α D hloop hdom hlinear v w hw)
  obtain ⟨C, hC, hCout⟩ := digraph_local_outneighborhood_cycle α D hloop v hv hc
  obtain ⟨w, hw⟩ := hv
  obtain ⟨p, hpv, hpw⟩ := hdom v w hw
  have hclean : ∀ a b, a ≠ b → D.Adj v a → D.Adj v b →
      ∀ x, D.Adj x a → D.Adj x b → x = v := by
    intro a b hab hva hvb x hxa hxb
    exact hlinear a b hab x v hxa hxb hva hvb
  exact digraph_clean_outneighborhood_cycle_packing_step α D k d hloop hori hdeg hpack v C hC hCout hclean p hpv
