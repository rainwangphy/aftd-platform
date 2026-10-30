import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointCanonicalMatching

/-!
# wild_joint_canonical_type

Topic: graphs   Node: 414b67b1ca6d

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The orbit type in {0,1,2,3} of a triple T relative to the fixed canonical matching: 0 (=A) if T contains a canonical edge and 0; 1 (=B) if 0 but no edge; 2 (=C) if an edge but not 0; 3 (=D) if neither.
-/

/-- Canonical orbit type (0=A,1=B,2=C,3=D) of triple T. -/
noncomputable def wild_joint_canonical_type (q : ℕ) (hq : 3 ≤ q) (T : Finset (Fin (3*q))) : ℕ := by classical exact if (∃ x ∈ T, ∃ y ∈ T, wild_joint_canonical_matching q x y) then (if (⟨0, by omega⟩ : Fin (3*q)) ∈ T then 0 else 2) else (if (⟨0, by omega⟩ : Fin (3*q)) ∈ T then 1 else 3)
