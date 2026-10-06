import AFTD.Prelude
import AFTD.Kb.Tcs.KarpReducible

/-!
# karp_reducible_refl

Topic: np_completeness   Node: 63feb1976b3f

Provenance: helper lemma. Karp 1972 (reflexivity of ≤_p); Mathlib: Turing.idComputableInPolyTime

Every language L over a finite alphabet Γ Karp-reduces to itself: the reduction is the identity function on words, which is computed by the identity Turing machine in a constant number of steps, and w ∈ L if and only if w ∈ L.
-/

/-- Karp reducibility is reflexive: every language over a finite alphabet reduces to itself by the identity. -/
theorem karp_reducible_refl {Γ : Type} [Fintype Γ] (L : Language Γ) : KarpReducible Γ Γ L L := by
  exact ⟨id, ⟨Turing.idComputableInPolyTime id⟩, fun _ => Iff.rfl⟩
