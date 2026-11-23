import AFTD.Prelude
import AFTD.Kb.Tcs.Biplane
import AFTD.Kb.Tcs.BiplaneFlag

/-!
# biplane_flag_fintype

Topic: combinatorics   Node: 8c7ffabcecf7

Provenance: formalization of a published result. Source: arXiv:2611.17855, Section 2.2

The type of flags of a biplane on finite point and line types is finite.
-/

/-- Fintype instance for flags of a biplane. -/
noncomputable instance biplane_flag_fintype {P L : Type*} [Fintype P] [Fintype L] (B : Biplane P L) : Fintype (BiplaneFlag B) := by
  classical
  exact Subtype.fintype _
