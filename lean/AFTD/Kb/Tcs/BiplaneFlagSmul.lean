import AFTD.Prelude
import AFTD.Kb.Tcs.Biplane
import AFTD.Kb.Tcs.BiplaneFlag
import AFTD.Kb.Tcs.BiplaneAutomorphismGroup

/-!
# biplane_flag_smul

Topic: combinatorics   Node: e1894bdb6beb

Provenance: formalization of a published result. Source: arXiv:2611.17855, Proposition 2.11

The natural scalar action of the automorphism group of a biplane on its flags.
-/

/-- Scalar action of automorphisms on flags. -/
instance biplane_flag_smul {P L : Type*} [Fintype P] [Fintype L] (B : Biplane P L) : SMul (biplane_automorphism_group B) (BiplaneFlag B) where
  smul g f := ⟨(g.1.1 f.1.1, g.1.2 f.1.2), (g.2 f.1.1 f.1.2).mpr f.2⟩
