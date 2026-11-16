import AFTD.Prelude
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op1370_block_forces_coordinate_pattern

Topic: combinatorics   Node: d2ce0070718d

Provenance: helper lemma. Coordinate blocker implication for OP-1370.

For strongly incomparable families, if a two-element set {x,y} and its complement both occur outside the family of S, then x belongs to S exactly when y does not.
-/

lemma op1370_block_forces_coordinate_pattern (n t : ℕ)
    (𝒜 : Fin t → Finset (Finset (Fin n))) (hinc : strongly_incomparable 𝒜)
    (i j k : Fin t) (hji : j ≠ i) (hki : k ≠ i) (x y : Fin n)
    (hw : ({x,y} : Finset (Fin n)) ∈ 𝒜 j)
    (hc : ({x,y} : Finset (Fin n))ᶜ ∈ 𝒜 k)
    (S : Finset (Fin n)) (hS : S ∈ 𝒜 i) : x ∈ S ↔ y ∉ S := by
  open Finset in
  classical
  constructor
  · intro hx hy
    have hsub : ({x,y} : Finset (Fin n)) ⊆ S := by
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    exact hinc j i hji {x,y} hw S hS hsub
  · intro hy
    by_contra hx
    have hsub : S ⊆ ({x,y} : Finset (Fin n))ᶜ := by
      intro a ha
      apply mem_compl.mpr
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hx (h ▸ ha), fun h => hy (h ▸ ha)⟩
    exact hinc i k hki.symm S hS ({x,y} : Finset (Fin n))ᶜ hc hsub
