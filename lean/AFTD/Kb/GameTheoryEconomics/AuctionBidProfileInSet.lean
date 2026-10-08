import AFTD.Prelude

/-!
# Auction.BidProfile.InSet

Topic: mechanism_design   Node: 7def94d3c745

Provenance: formalization of a published result. Source: EconCSLib, `Auction.BidProfile.InSet`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Each bid lies in the per-agent admissible set. For a family of strategy sets $S_i \subseteq V$, asserts $\forall i.\; b_i \in S_i$. Captures heterogeneous strategy spaces.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I V : Type*} in
/-- Each bid lies in the per-agent admissible set. For a family of strategy sets $S_i \subseteq V$, asserts $\forall i.\; b_i \in S_i$. Captures heterogeneous strategy spaces. -/
def Auction.BidProfile.InSet (b : I → V) (S : I → Set V) : Prop :=
  ∀ i, b i ∈ S i
