import AFTD.Prelude
import AFTD.Kb.Tcs.IsResolutionRefutation
import AFTD.Kb.Tcs.IsResolutionDerivation
import AFTD.Kb.Tcs.CnfLit

/-!
# is_resolution_refutation_mono

Topic: proof_complexity   Node: 778c576ba08d

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

Monotonicity of resolution refutations: if F1 is a subset of F2, any resolution refutation of F1 is also a resolution refutation of F2 of identical length.
-/

/-- Monotonicity of resolution refutations under clause addition. -/
theorem is_resolution_refutation_mono {V : Type*} (F₁ F₂ : Finset (Finset (CnfLit V))) (π : List (Finset (CnfLit V))) (hsub : F₁ ⊆ F₂) (href : is_resolution_refutation F₁ π) : is_resolution_refutation F₂ π := by
  rcases href with ⟨hder, hlast⟩
  refine ⟨?_, hlast⟩
  intro i
  rcases hder i with h1 | h2 | h3
  · left
    exact hsub h1
  · right; left
    exact h2
  · right; right
    exact h3
