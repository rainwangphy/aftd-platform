import AFTD.Prelude

/-!
# QuantumMechanics.FiniteHilbertSpace

Topic: quantum_mechanics   Node: 0221d0d1cb5e

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteHilbertSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Hilbert space of a finite target quantum mechanical system whose target is a finite type `d` with decidable equality. It is defined as a structure with a single field `val`, wrapping an element of `EuclideanSpace ℂ d` — the space of functions `d → ℂ` carrying the `L²` inner product `⟪ψ, φ⟫ = ∑ i, conj (ψ i) * φ i`. Using a structure in preference to `EuclideanSpace ℂ d` itself makes the Hilbert space of states a type of its own, with its own API and the notation `𝓗[d]`. Being finite dimensional, it is automatically a complete inner product space, that is, a genuine Hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The Hilbert space of a finite target quantum mechanical system whose target is a finite type `d` with decidable equality. It is defined as a structure with a single field `val`, wrapping an element of `EuclideanSpace ℂ d` — the space of functions `d → ℂ` carrying the `L²` inner product `⟪ψ, φ⟫ = ∑ i, conj (ψ i) * φ i`. Using a structure in preference to `EuclideanSpace ℂ d` itself makes the Hilbert space of states a type of its own, with its own API and the notation `𝓗[d]`. Being finite dimensional, it is automatically a complete inner product space, that is, a genuine Hilbert space. -/
@[ext]
structure QuantumMechanics.FiniteHilbertSpace (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying element of `EuclideanSpace ℂ d`. -/
  val : EuclideanSpace ℂ d
