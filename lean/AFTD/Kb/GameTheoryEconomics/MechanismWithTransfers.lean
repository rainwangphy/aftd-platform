import AFTD.Prelude

/-!
# MechanismWithTransfers

Topic: mechanism_design   Node: 77e8f243dcdc

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A mechanism with monetary transfers. - `I` — agents - `T` — report/type space of each agent - `A` — allocation space - `P` — payment space The mechanism stores only how reports determine allocations and payments. Utility is imposed later, for example by quasi-linear utility or some richer domain-specific construction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A mechanism with monetary transfers. - `I` — agents - `T` — report/type space of each agent - `A` — allocation space - `P` — payment space The mechanism stores only how reports determine allocations and payments. Utility is imposed later, for example by quasi-linear utility or some richer domain-specific construction. -/
structure MechanismWithTransfers
    (I : Type*) (T : I → Type*) (A : Type*) (P : Type*) where
  /-- The allocation rule: given reports, choose an allocation. -/
  allocationRule : (∀ i, T i) → A
  /-- The payment rule: given reports, determine each agent's payment. -/
  paymentRule : (∀ i, T i) → I → P
