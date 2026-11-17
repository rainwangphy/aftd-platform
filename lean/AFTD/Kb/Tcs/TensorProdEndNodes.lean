import AFTD.Prelude

/-!
# tensor_prod_end_nodes

Topic: quantum   Node: 931819de7608

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. III.1

Given a family of d × d complex matrices A : Fin n → Matrix (Fin d) (Fin d) ℂ, their tensor product on (ℂ^d)^⊗n is the matrix indexed by (Fin n → Fin d) with entries at (u, v) given by ∏ i : Fin n, A i (u i) (v i).
-/

/-- The tensor product of n local end-node observables on (C^d)^n. -/
def tensor_prod_end_nodes (n d : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := fun u v => ∏ i : Fin n, A i (u i) (v i)
