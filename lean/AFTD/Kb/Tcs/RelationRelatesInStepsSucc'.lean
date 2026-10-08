import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsSucc
import AFTD.Kb.Tcs.RelationRelatesInStepsZeroIff
import AFTD.Kb.Tcs.RelationRelatesInStepsZero

/-!
# Relation.RelatesInSteps.succ'

Topic: algorithms   Node: 84b8906816f5

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.succ'`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.succ'
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesInSteps.succ' {a b : α} : ∀ {n : ℕ}, RelatesInSteps r a b (n + 1) →
    ∃ t', r a t' ∧ RelatesInSteps r t' b n := by
  intro n h
  obtain ⟨t', hsteps, hstep⟩ := succ h
  cases n with
  | zero =>
    rw [zero_iff] at hsteps
    subst hsteps
    exact ⟨b, hstep, .refl _⟩
  | succ k' =>
    obtain ⟨t''', h_red''', h_steps'''⟩ := succ' hsteps
    exact ⟨t''', h_red''', .tail _ _ b k' h_steps''' hstep⟩
