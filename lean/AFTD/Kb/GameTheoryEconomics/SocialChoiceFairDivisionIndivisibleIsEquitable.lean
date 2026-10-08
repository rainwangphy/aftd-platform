import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsEquitable
import AFTD.Kb.Tcs.G

/-!
# SocialChoice.FairDivision.Indivisible.IsEquitable

Topic: fair_division   Node: fc3a3af531b4

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsEquitable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equitable (EQ): all agents achieve the same utility from their own bundle. `∀ i j, v_i(A_i) = v_j(A_j)`. Equitability requires comparable utilities across agents — it is most meaningful when valuations are normalized so every agent assigns total value 1 to all goods combined. Equitability is incomparable with envy-freeness: - EF does not imply EQ: agents may have different utilities from their bundles even with no envy (e.g., agent 0 gets a good worth 10 to them, agent 1 gets a good worth 7 to them; if neither envies the other, EF holds but EQ fails). - EQ does not imply EF: equal utilities do not prevent an agent from preferring the other's bundle (if agent 0 values both bundles at 5, they may still prefer agent 1's bundle by their own measure). For divisible goods (normalized valuations), equitable+EF allocations always exist (Alon 1987, n²−n cuts suffice). For indivisible goods, equitable allocations may not exist. [BCM Ch.12; Proc Ch.13]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- Equitable (EQ): all agents achieve the same utility from their own bundle. `∀ i j, v_i(A_i) = v_j(A_j)`. Equitability requires comparable utilities across agents — it is most meaningful when valuations are normalized so every agent assigns total value 1 to all goods combined. Equitability is incomparable with envy-freeness: - EF does not imply EQ: agents may have different utilities from their bundles even with no envy (e.g., agent 0 gets a good worth 10 to them, agent 1 gets a good worth 7 to them; if neither envies the other, EF holds but EQ fails). - EQ does not imply EF: equal utilities do not prevent an agent from preferring the other's bundle (if agent 0 values both bundles at 5, they may still prefer agent 1's bundle by their own measure). For divisible goods (normalized valuations), equitable+EF allocations always exist (Alon 1987, n²−n cuts suffice). For indivisible goods, equitable allocations may not exist. [BCM Ch.12; Proc Ch.13] -/
abbrev SocialChoice.FairDivision.Indivisible.IsEquitable (v : Valuation N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsEquitable v.val A
