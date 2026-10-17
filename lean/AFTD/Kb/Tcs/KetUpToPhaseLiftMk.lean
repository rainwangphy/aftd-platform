import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetPhaseEquiv
import AFTD.Kb.Tcs.KetUpToPhaseLift
import AFTD.Kb.Tcs.KetUpToPhaseMk
import AFTD.Kb.Tcs.KetIsProdProd
import AFTD.Kb.Tcs.KetNotIsEntangledProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# KetUpToPhase.lift_mk

Topic: quantum   Node: 091d1424ee7b

Provenance: formalization of a published result. Source: QuantumInfo, `KetUpToPhase.lift_mk`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KetUpToPhase.lift_mk
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
@[simp]
theorem KetUpToPhase.lift_mk {α : Sort*} (f : Ket d → α)
    (hf : ∀ ψ φ, Ket.PhaseEquiv.r ψ φ → f ψ = f φ) (ψ : Ket d) :
    KetUpToPhase.lift f hf (KetUpToPhase.mk ψ) = f ψ := rfl
