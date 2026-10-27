import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityOfProperColoring
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityLeDegree

/-!
# maxcut_strong_equilibrium_of_proper_coloring

Topic: equilibria   Node: d97d33564d48

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

A proper k-colouring of a finite simple graph is a strong equilibrium of the Max-k-Cut game: every player already has utility equal to its degree, so no coalition can make any of its members strictly better off.
-/

/-- Any proper k-colouring is a strong equilibrium of the Max-k-Cut game. -/
theorem maxcut_strong_equilibrium_of_proper_coloring {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (h : ∀ v w, G.Adj v w → σ v ≠ σ w) : is_maxcut_strong_equilibrium G σ := by
  intro S τ hdev
  obtain ⟨hne, -, himp⟩ := hdev
  obtain ⟨v, hv⟩ := hne
  have h1 := himp v hv
  have h2 : maxcut_utility G σ v = G.degree v :=
    maxcut_utility_of_proper_coloring G σ h v
  have h3 := maxcut_utility_le_degree G τ v
  omega
