import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasIsNonDegenerate

/-!
# dual_melas_is_non_degenerate_one

Topic: information   Node: 6acd64aef4cb

Provenance: helper lemma. arXiv:2610.38017 Definition 3

For every field $F$ with an algebra structure over $\mathbb{Z}/2\mathbb{Z}$ (i.e., of characteristic 2) and every element $\alpha \in F$, the constant polynomial $1 \in (\mathbb{Z}/2\mathbb{Z})[X]$ is non-degenerate with respect to $\alpha$.
-/

/-- The constant polynomial 1 is non-degenerate. -/
theorem dual_melas_is_non_degenerate_one {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (α : F) :
    dual_melas_is_non_degenerate α (1 : Polynomial (ZMod 2)) := by
  unfold dual_melas_is_non_degenerate
  simp
