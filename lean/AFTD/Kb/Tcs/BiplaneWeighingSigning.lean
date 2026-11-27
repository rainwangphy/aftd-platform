import AFTD.Prelude
import AFTD.Kb.Tcs.Biplane
import AFTD.Kb.Tcs.BiplaneFlag

/-!
# biplane_weighing_signing

Topic: combinatorics   Node: 008d3f391d73

Provenance: formalization of a published result. Source: arXiv:2611.17855 (On configurations that are nearly generalised polygons), Section 2.2 (signing and weighing signing of a biplane).

A weighing signing of a biplane B (points P, lines L, block size B.k) is a function σ from the flags (incident point-line pairs) to the integers taking only the values 1 and −1, such that the L × P integer matrix W with W(l, p) = σ(p, l) when p is on l and 0 otherwise satisfies W · Wᵀ = k · I (the L × L identity scaled by k).
-/

open Classical in
def biplane_weighing_signing {P L : Type*} [Fintype P] [Fintype L] (B : Biplane P L)
    (σ : BiplaneFlag B → ℤ) : Prop :=
  (∀ f, σ f = 1 ∨ σ f = -1) ∧
    (Matrix.of fun (l : L) (p : P) => if h : B.inc p l then σ ⟨(p, l), h⟩ else 0) *
      (Matrix.of fun (l : L) (p : P) => if h : B.inc p l then σ ⟨(p, l), h⟩ else 0).transpose =
        (B.k : ℤ) • (1 : Matrix L L ℤ)
