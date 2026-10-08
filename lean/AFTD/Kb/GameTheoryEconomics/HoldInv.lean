import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState

/-!
# HoldInv

Topic: matching_markets   Node: cbef16df6e58

Provenance: formalization of a published result. Source: EconCSLib, `HoldInv`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**HoldInv** (Held → Proposed): if woman `p` currently holds man `j`, then `j` must already have proposed to `p` — i.e., `p` is in the proposed-prefix `(m.prefs j).take (s.nextChoice j)` of `j`'s preference list. This is the **converse direction** of [`JInv`]: `JInv` says proposed ⇒ held; `HoldInv` says held ⇒ proposed. Together they make the two-sided correspondence between cursors and holdings airtight. `HoldInv` is the one the stability proof's "the holder must be at least as preferred as the blocker" step relies on, via `RSInv` — see the proof sketch of [`galeShapley_isStable`] and the preservation lemma [`holdinv_step`].
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- **HoldInv** (Held → Proposed): if woman `p` currently holds man `j`, then `j` must already have proposed to `p` — i.e., `p` is in the proposed-prefix `(m.prefs j).take (s.nextChoice j)` of `j`'s preference list. This is the **converse direction** of [`JInv`]: `JInv` says proposed ⇒ held; `HoldInv` says held ⇒ proposed. Together they make the two-sided correspondence between cursors and holdings airtight. `HoldInv` is the one the stability proof's "the holder must be at least as preferred as the blocker" step relies on, via `RSInv` — see the proof sketch of [`galeShapley_isStable`] and the preservation lemma [`holdinv_step`]. -/
def HoldInv (m : Preferences n) (s : DAState n) : Prop :=
  ∀ j p : Fin n, s.holding p = some j → p ∈ (m.prefs j).take (s.nextChoice j)
