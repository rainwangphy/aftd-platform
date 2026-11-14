import AFTD.Prelude
import AFTD.Kb.Tcs.RevComp

/-!
# scs_rc_opt

Topic: approximation   Node: 29d0a3bfd4bb

Provenance: formalization of a published result. Source: arXiv:2611.16573, Definition 5

The optimum of the Shortest Common Superstring with Reverse Complements problem: the least length of a string that contains s or rc(s) as a substring for every s in S.
-/

/-- |OPT(S)| for SCS-RC: the least length of a string containing s or rc(s) as a substring for every s ∈ S. -/
noncomputable def scs_rc_opt {Γ : Type*} (cm : Γ → Γ) (S : Finset (List Γ)) : ℕ :=
  sInf {n | ∃ u : List Γ, u.length = n ∧ ∀ s ∈ S, s <:+: u ∨ rev_comp cm s <:+: u}
