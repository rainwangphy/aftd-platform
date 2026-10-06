import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# is_maxcut_strong_deviation

Topic: equilibria   Node: 470ed4926df9

Provenance: formalization of a published result. Source: arXiv:2610.04948 (Social Optimality Does Not Imply Coalitional Stability in Unweighted Max-k-Cut Games), Sec. 1; the Lean version does not require every member to change color, which the paper notes is without loss of generality

A strong deviation from σ is a nonempty coalition S ⊆ V with a coloring τ agreeing with σ outside S such that u_v(τ) > u_v(σ) for every v ∈ S. (The paper also asks every member to change color; it notes this is without loss of generality, and the resulting notion of strong equilibrium is the same.)
-/

/-- A strong deviation from `σ` in the Max-k-Cut game: a nonempty coalition `S` and a coloring `τ` that agrees with `σ` outside `S` and strictly raises the utility of every member of `S`. -/
def is_maxcut_strong_deviation {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (S : Finset V) (τ : V → Fin k) : Prop :=
  S.Nonempty ∧ (∀ v, v ∉ S → τ v = σ v) ∧
    ∀ v ∈ S, maxcut_utility G σ v < maxcut_utility G τ v
