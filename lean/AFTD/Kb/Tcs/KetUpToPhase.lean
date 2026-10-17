import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetPhaseEquiv
import AFTD.Kb.Tcs.KetIsProdProd
import AFTD.Kb.Tcs.KetNotIsEntangledProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# KetUpToPhase

Topic: quantum   Node: a4ab7e0fc3d2

Provenance: formalization of a published result. Source: QuantumInfo, `KetUpToPhase`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of `Ket`s up to a global phase equivalence, as given by `Ket.PhaseEquiv`. In particular, `MState`s really only care about a KetUpToPhase, and not Kets themselves.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
variable (d) in
/-- The type of `Ket`s up to a global phase equivalence, as given by `Ket.PhaseEquiv`. In particular, `MState`s really only care about a KetUpToPhase, and not Kets themselves. -/
noncomputable def KetUpToPhase :=
  @Quotient (Ket d) Ket.PhaseEquiv
