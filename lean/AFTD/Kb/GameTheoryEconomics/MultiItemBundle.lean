import AFTD.Prelude

/-!
# MultiItemBundle

Topic: mechanism_design   Node: c5277adbe9df

Provenance: formalization of a published result. Source: EconCSLib, `MultiItemBundle`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multi-item auction with `k` distinct items. An agent bundle is a finite subset of the `k` items, represented as `Finset (Fin k)`. A full allocation assigns one bundle to each agent. Agents report valuation functions over full allocation profiles, so this is the specialization of `MultipleParameterMechanism` to bundle allocations. Feasibility (no item sold twice) is a separate predicate; see `IsFeasible`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A multi-item auction with `k` distinct items. An agent bundle is a finite subset of the `k` items, represented as `Finset (Fin k)`. A full allocation assigns one bundle to each agent. Agents report valuation functions over full allocation profiles, so this is the specialization of `MultipleParameterMechanism` to bundle allocations. Feasibility (no item sold twice) is a separate predicate; see `IsFeasible`. -/
def MultiItemBundle (k : ℕ) := Finset (Fin k)
