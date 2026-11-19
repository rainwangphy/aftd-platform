import AFTD.Prelude
import AFTD.Kb.Tcs.IsTwoDimReedSolomonCode

/-!
# is_two_dim_reed_solomon_code_of_injective

Topic: information   Node: e27851f068aa

Provenance: helper lemma. arXiv:2611.21275 Definition 5

For any field $F$ and any injective function $\alpha : \mathrm{Fin}\,n \to F$, the $F$-submodule spanned by the set containing the all-ones vector and $\alpha$ is a two-dimensional Reed-Solomon code.
-/

/-- The span of the all-ones vector and an injective evaluation vector is a two-dimensional Reed-Solomon code. -/
lemma is_two_dim_reed_solomon_code_of_injective {n : ℕ} {F : Type*} [Field F]
    (α : Fin n → F) (hα : Function.Injective α) :
    is_two_dim_reed_solomon_code (Submodule.span F {fun _ => (1 : F), α}) := ⟨α, hα, rfl⟩
