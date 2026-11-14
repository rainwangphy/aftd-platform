import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteUniversallyLocallyEncodable
import AFTD.Kb.Tcs.IsBipartiteLocallyEncodable

/-!
# bipartite_universally_locally_encodable_one_one

Topic: quantum   Node: 9045acfbd9f9

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec. II.1

Universal local encodability holds for 1 × 1 bipartite quantum systems: bipartite_universally_locally_encodable 1 1.
-/

/-- The 1 × 1 bipartite quantum system is universally locally encodable. -/
theorem bipartite_universally_locally_encodable_one_one :
    bipartite_universally_locally_encodable 1 1 := by
  have : Unique (Fin 1 × Fin 1) := ⟨⟨(default, default)⟩, by intro ⟨a, b⟩; simp [Unique.eq_default a, Unique.eq_default b]⟩
  intro ψ hψ
  unfold is_bipartite_locally_encodable
  refine ⟨FiniteDimensional.orthonormalBasisSingleton (Fin 1 × Fin 1) ℂ (by simp) ψ hψ, ?_⟩
  intro j
  refine ⟨1, 1, ?_⟩
  simp
