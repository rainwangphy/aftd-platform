import AFTD.Prelude

/-!
# dual_melas_seq

Topic: information   Node: 248acc99cc0f

Provenance: formalization of a published result. Source: scout/2610-38017-on-the-b-symbol-weight-distribution-of-dual-melas-codes-and.md:1069

For a field F equipped with an algebra structure over ZMod 2 and finite-dimensional over ZMod 2, elements α, c : F, and index i : ℕ, dual_melas_seq α c i is defined as the algebra trace from F to ZMod 2 of the element α ^ i + c * (α⁻¹) ^ i.
-/

/-- The dual Melas binary sequence defined by s_i = Tr(α^i + c α^(-i)). -/
noncomputable def dual_melas_seq {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F] (α c : F) (i : ℕ) : ZMod 2 := Algebra.trace (ZMod 2) F (α ^ i + c * (α⁻¹) ^ i)
