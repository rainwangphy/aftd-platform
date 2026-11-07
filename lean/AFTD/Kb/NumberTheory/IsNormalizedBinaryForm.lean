import AFTD.Prelude

/-!
# is_normalized_binary_form

Topic: elementary_number_theory   Node: 090c4442e40d

Provenance: formalization of a published result. Source: arXiv:2611.02063 Section 3

A linear functional $\nu : V \to \mathbb{F}_2$ on a vector space $V$ over $\mathbb{F}_2$ is normalized at $u \in V$ if $\nu(u) = 1$.
-/

/-- A binary linear form on V is normalized at u if it evaluates to 1 at u. -/
def is_normalized_binary_form {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (u : V) (ν : V →ₗ[ZMod 2] ZMod 2) : Prop := ν u = 1
