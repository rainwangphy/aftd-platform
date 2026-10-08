import AFTD.Prelude

/-!
# GS.pref_list_mem

Topic: matching_markets   Node: f832db8594c6

Provenance: formalization of a published result. Source: EconCSLib, `GS.pref_list_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every element of `Fin n` appears in a full-permutation list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- Every element of `Fin n` appears in a full-permutation list. -/
lemma GS.pref_list_mem {n : ℕ} (l : List (Fin n)) (hnd : l.Nodup) (hlen : l.length = n)
    (x : Fin n) : x ∈ l := by
  rw [← List.mem_toFinset]
  exact (Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnd, hlen,
    Fintype.card_fin])).symm ▸ Finset.mem_univ _
