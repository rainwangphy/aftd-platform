import AFTD.Prelude
import AFTD.Kb.Physics.F2CharacterToDual
import AFTD.Kb.Physics.F2DualToCharacter
import AFTD.Kb.Physics.F2RealCharacterValues

/-!
# f2_real_character_extends

Topic: quantum_mechanics   Node: 41305d67f7c1

Provenance: helper lemma. Binary character infrastructure for the OP-827 supported-kernel entropy reduction.

Every real-valued additive character on a subspace of a binary vector space extends to the whole space.
-/

theorem f2_real_character_extends {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (L : Submodule (ZMod 2) M) (χ : AddChar L ℝ) :
    ∃ ψ : AddChar M ℝ, ∀ x : L, ψ x.1 = χ x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (f2_character_to_dual χ)
  refine ⟨f2_dual_to_character g, ?_⟩
  intro x
  have hval : g x.1 = f2_character_to_dual χ x := LinearMap.congr_fun hg x
  rcases f2_real_character_values χ x with hx | hx <;>
  norm_num [f2_dual_to_character, hval, f2_character_to_dual, hx]
