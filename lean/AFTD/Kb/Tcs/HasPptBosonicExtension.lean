import AFTD.Prelude

/-!
# has_ppt_bosonic_extension

Topic: quantum   Node: 747b7188e49b

Provenance: formalization of a published result. Source: The PPT bosonic (symmetric-subspace) k-extension of arXiv:quant-ph/0308032 (complete family of separability criteria), Sections III-IV; stated for OP-2299. The Lean asks the marginal condition for every copy B_i (equivalent to copy B_1 by the symmetry) and lists the partial transposes by the subset S of copies of B that is transposed (transposing a set of parties or its complement differ by a full transpose, so these are all bipartitions).

With dA dB k : ℕ explicit arguments, in this order, and ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ, the proposition that ρ has a PPT bosonic k-extension: there exists a matrix Ω : Matrix (Fin dA × (Fin k → Fin dB)) (Fin dA × (Fin k → Fin dB)) ℂ (an operator on A ⊗ B_1 ⊗ ... ⊗ B_k, a basis state of the k copies of B being a function Fin k → Fin dB) satisfying the conjunction of three conditions. (1) Bosonic support: for every permutation π : Equiv.Perm (Fin k) and all indices p, q, Ω (p.1, p.2 ∘ π) q = Ω p q (permuting the k copies of B in the row index leaves Ω unchanged, i.e. Ω is supported on A ⊗ Sym^k). (2) Marginal: for every copy i : Fin k and all p, q : Fin dA × Fin dB, ρ p q equals the sum over all f : Fin k → Fin dB of (if f i = p.2 then Ω (p.1, f) (q.1, Function.update f i q.2) else 0), i.e. tracing out all copies of B except the i-th gives ρ. (3) PPT across every bipartition: for every set S : Finset (Fin k) of copies of B, the partial transpose of Ω on the copies in S, namely the matrix whose (p, q) entry is Ω (p.1, fun i => if i ∈ S then q.2 i else p.2 i) (q.1, fun i => if i ∈ S then p.2 i else q.2 i), is positive semidefinite (Matrix.PosSemidef over ℂ); S = ∅ says that Ω itself is positive semidefinite.
-/

/-- `ρ` on `A ⊗ B` has a PPT bosonic `k`-extension: an operator on `A ⊗ B^{⊗k}` supported on `A ⊗ Sym^k`, with marginal `ρ` on `A` and each copy of `B`, all of whose partial transposes are positive semidefinite. -/
def has_ppt_bosonic_extension (dA dB k : ℕ)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : Prop :=
  ∃ Ω : Matrix (Fin dA × (Fin k → Fin dB)) (Fin dA × (Fin k → Fin dB)) ℂ,
    (∀ (π : Equiv.Perm (Fin k)) (p q : Fin dA × (Fin k → Fin dB)),
        Ω (p.1, p.2 ∘ π) q = Ω p q) ∧
    (∀ (i : Fin k) (p q : Fin dA × Fin dB),
        ρ p q = ∑ f : Fin k → Fin dB,
          if f i = p.2 then Ω (p.1, f) (q.1, Function.update f i q.2) else 0) ∧
    (∀ S : Finset (Fin k), open scoped ComplexOrder in
        (Matrix.of fun (p q : Fin dA × (Fin k → Fin dB)) =>
          Ω (p.1, fun i => if i ∈ S then q.2 i else p.2 i)
            (q.1, fun i => if i ∈ S then p.2 i else q.2 i)).PosSemidef)
