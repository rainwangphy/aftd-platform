import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAlice
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_run

Topic: communication   Node: 8317c83bfb68

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Evaluation of the complete Alice-query tree. Fix a depth $d \in \bbn$, a family of binary query functions $\mathrm{query}_i : X \to
\mathrm{Bool}$ for $i \in \mathrm{Fin}\,d$, and a family of deterministic protocols
$Q(b)$ indexed by bit patterns $b : \mathrm{Fin}\,d \to \mathrm{Bool}$. Then for every
pair of inputs $x : X$ and $y : Y$, the protocol that first has Alice read the $d$ query
bits in sequence and then runs $Q$ on the collected pattern evaluates on $(x,y)$ to the
same value as the single protocol $Q\bigl(i \mapsto \mathrm{query}_i(x)\bigr)$ evaluated
on $(x,y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Running the complete tree of depth `d` on `(x, y)` is the same as running the continuation `Q` at the bit vector `i ↦ query i x` on `(x, y)`. -/
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_run (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) (x : X) (y : Y) :
    (completeTreeAlice d query Q).run x y = (Q (fun i => query i x)).run x y := by
  induction d with
  | zero =>
    simp only [completeTreeAlice]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeAlice, Deterministic.Protocol.run]
    rw [ih]
    -- Goal: (Q (Fin.cons (query 0 x) ...)).run x y = (Q (fun i => query i x)).run x y
    -- Suffices to show the arguments to Q are equal
    have :
        Fin.cons (query 0 x) (fun i => (query ∘ Fin.succ) i x) =
        fun i => query i x := by
      exact Fin.cons_self_tail (fun i => query i x)
    rw [this]
