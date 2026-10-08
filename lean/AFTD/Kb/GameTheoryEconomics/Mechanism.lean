import AFTD.Prelude

/-!
# Mechanism

Topic: mechanism_design   Node: bbd01fc23f9d

Provenance: formalization of a published result. Source: EconCSLib, `Mechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A (direct revelation) mechanism. - `I` — the set of agents (indices) - `T` — the type space of each agent - `O` — the outcome space A mechanism maps a profile of reported types to an outcome. In a *direct* mechanism, the message/preference space equals the type space, so agent `i` reports elements of `T i`. This is the most general definition. Specializations (auctions, voting rules, matching mechanisms) arise by choosing appropriate `T`, `O`, and utility functions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A (direct revelation) mechanism. - `I` — the set of agents (indices) - `T` — the type space of each agent - `O` — the outcome space A mechanism maps a profile of reported types to an outcome. In a *direct* mechanism, the message/preference space equals the type space, so agent `i` reports elements of `T i`. This is the most general definition. Specializations (auctions, voting rules, matching mechanisms) arise by choosing appropriate `T`, `O`, and utility functions. -/
structure Mechanism (I : Type*) (T : I → Type*) (O : Type*) where
  /-- The outcome function: given all agents' reports, choose an outcome. -/
  outcome : (∀ i, T i) → O
