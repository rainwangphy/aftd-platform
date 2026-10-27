import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard

/-!
# maxcut_utility_of_proper_coloring

Topic: equilibria   Node: 1cce0aa53e6d

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

If σ is a proper k-colouring of a finite simple graph G, then each player v has Max-k-Cut utility equal to its degree: maxcut_utility G σ v = G.degree v.
-/

/-- At any proper k-colouring of a graph G, every player v achieves maximal possible utility equal to its degree G.degree v, because it has zero monochromatic neighbours. -/
theorem maxcut_utility_of_proper_coloring {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (h : ∀ v w, G.Adj v w → σ v ≠ σ w) (v : V) : maxcut_utility G σ v = G.degree v := by
  have hsum := maxcut_utility_add_monochromatic_card G σ v
  have hempty : (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) = ∅ := by
    apply Finset.filter_false_of_mem
    intro w _ hw
    exact h v w hw.1 hw.2.symm
  rw [hempty] at hsum
  simp at hsum
  exact hsum
