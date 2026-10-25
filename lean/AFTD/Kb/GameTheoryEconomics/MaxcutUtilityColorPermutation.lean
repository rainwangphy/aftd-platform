import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_utility_color_permutation

Topic: equilibria   Node: d496d9a24d02

Provenance: helper lemma. Color-symmetry helper for the OP-89 pinned-twin refutation criterion.

Permuting all color labels preserves every player’s utility in the Max-k-Cut game.
-/

theorem maxcut_utility_color_permutation {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ : V → Fin k) (p : Equiv.Perm (Fin k)) (v : V) :
    maxcut_utility G (fun w => p (σ w)) v = maxcut_utility G σ v := by
  classical
  unfold maxcut_utility
  congr 1
  ext w
  simp
