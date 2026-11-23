import AFTD.Prelude
import AFTD.Kb.Tcs.Biplane
import AFTD.Kb.Tcs.BiplaneFlag
import AFTD.Kb.Tcs.BiplaneAutomorphismGroup
import AFTD.Kb.Tcs.BiplaneFlagSmul

/-!
# biplane_flag_mul_action

Topic: combinatorics   Node: 153760902364

Provenance: formalization of a published result. Source: arXiv:2611.17855, Proposition 2.11

The action of the automorphism group of a biplane on flags is a group action.
-/

/-- MulAction of automorphisms on flags. -/
instance biplane_flag_mul_action {P L : Type*} [Fintype P] [Fintype L] (B : Biplane P L) : MulAction (biplane_automorphism_group B) (BiplaneFlag B) where
  one_smul f := Subtype.ext (Prod.ext (Equiv.Perm.one_apply f.1.1) (Equiv.Perm.one_apply f.1.2))
  mul_smul g h f := Subtype.ext (Prod.ext (Equiv.Perm.mul_apply g.1.1 h.1.1 f.1.1) (Equiv.Perm.mul_apply g.1.2 h.1.2 f.1.2))
