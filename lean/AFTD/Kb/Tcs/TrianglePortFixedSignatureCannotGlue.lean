import AFTD.Prelude

/-!
# triangle_port_fixed_signature_cannot_glue

Topic: combinatorics   Node: 6d16308b79ef

Provenance: helper lemma. Elementary fixed-signature obstruction for the local compatibility condition of arXiv:2610.41950, Section 2.

A color map fixing color 1 leaves the pair {1,2} intersecting its image, so two copies of the indicated fixed exposed pair cannot be joined while preserving its boundary color.
-/

theorem triangle_port_fixed_signature_cannot_glue (f : Fin 6 → Fin 6) (hf : f 1 = 1) : ∃ c : Fin 6, c ∈ ({1,2} : Set (Fin 6)) ∧ c ∈ f '' ({1,2} : Set (Fin 6)) := by
  refine ⟨1, by simp, ?_⟩
  exact ⟨1, by simp, hf⟩
