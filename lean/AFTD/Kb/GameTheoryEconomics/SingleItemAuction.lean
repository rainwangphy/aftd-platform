import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.Tcs.V

/-!
# SingleItemAuction

Topic: mechanism_design   Node: bce9f460debb

Provenance: formalization of a published result. Source: EconCSLib, `SingleItemAuction`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A single-item auction. One indivisible item is for sale. Each agent reports a scalar bid of type `V`. The allocation is `Option I`: - `some i` — bidder `i` receives the item - `none` — the item is withheld (reserve price not met, etc.) Which bidder wins, or whether anyone wins, is determined by the allocation rule of the specific mechanism. This structure imposes no winner-selection policy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A single-item auction. One indivisible item is for sale. Each agent reports a scalar bid of type `V`. The allocation is `Option I`: - `some i` — bidder `i` receives the item - `none` — the item is withheld (reserve price not met, etc.) Which bidder wins, or whether anyone wins, is determined by the allocation rule of the specific mechanism. This structure imposes no winner-selection policy. -/
structure SingleItemAuction (I : Type*) (V : Type*) (P : Type*)
    extends MechanismWithTransfers I (fun _ => V) (Option I) P
