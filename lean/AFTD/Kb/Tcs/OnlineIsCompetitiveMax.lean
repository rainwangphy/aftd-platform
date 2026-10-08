import AFTD.Prelude
import AFTD.Kb.Tcs.F

/-!
# Online.IsCompetitiveMax

Topic: online_algorithms   Node: c472033d9a2f

Provenance: formalization of a published result. Source: EconCSLib, `Online.IsCompetitiveMax`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`c`-competitive for a **maximisation** objective: the algorithm's value on every request sequence is at least `c · opt`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α F : Type*} in
/-- `c`-competitive for a **maximisation** objective: the algorithm's value on every request sequence is at least `c · opt`. -/
def Online.IsCompetitiveMax [Mul F] [LE F]
    (value opt : List α → F) (c : F) : Prop :=
  ∀ reqs, c * opt reqs ≤ value reqs
