import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetPhaseEquiv
import AFTD.Kb.Tcs.KetUpToPhase
import AFTD.Kb.Tcs.KetIsProdProd
import AFTD.Kb.Tcs.KetNotIsEntangledProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# KetUpToPhase.lift

Topic: quantum   Node: a920b12216df

Provenance: formalization of a published result. Source: QuantumInfo, `KetUpToPhase.lift`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lift a function on `Ket d` to `KetUpToPhase d`, given that it respects phase equivalence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
/-- Lift a function on `Ket d` to `KetUpToPhase d`, given that it respects phase equivalence. -/
noncomputable def KetUpToPhase.lift {α : Sort*} (f : Ket d → α)
    (hf : ∀ ψ φ, Ket.PhaseEquiv.r ψ φ → f ψ = f φ) : KetUpToPhase d → α :=
  @Quotient.lift _ _ Ket.PhaseEquiv f hf
