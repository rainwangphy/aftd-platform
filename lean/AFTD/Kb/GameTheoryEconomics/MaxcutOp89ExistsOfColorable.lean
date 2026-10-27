import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalOfProperColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfProperColoring
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_op89_exists_of_colorable

Topic: equilibria   Node: 510f57e2b44d

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

If a finite simple graph admits a proper k-colouring, then the unweighted Max-k-Cut game on (G,k) has an optimal colouring that is a strong equilibrium; in particular OP-89 holds for every graph with χ(G) ≤ k, regardless of the number of vertices or of the maximum degree.
-/

/-- OP-89 holds for every graph admitting a proper k-colouring (χ(G) ≤ k), with no bound on |V| or on the maximum degree. -/
theorem maxcut_op89_exists_of_colorable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hcol : G.Colorable k) : maxcut_has_optimal_strong_equilibrium G k := by
  obtain ⟨σ⟩ := hcol
  have hprop : ∀ v w, G.Adj v w → σ.toFun v ≠ σ.toFun w := by
    intro v w hadj
    simpa using σ.map_rel hadj
  exact ⟨σ.toFun, maxcut_optimal_of_proper_coloring G σ.toFun hprop,
                 maxcut_strong_equilibrium_of_proper_coloring G σ.toFun hprop⟩
