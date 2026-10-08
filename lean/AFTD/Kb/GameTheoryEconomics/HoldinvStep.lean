import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.HoldInv
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSNotIsFreeIff
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcHeld
import AFTD.Kb.GameTheoryEconomics.PlFreeProps
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcFree
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.GSDaStepHolding

/-!
# holdinv_step

Topic: matching_markets   Node: 050a7c14be88

Provenance: formalization of a published result. Source: EconCSLib, `holdinv_step`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`HoldInv` is preserved by one DA step. Proof structure: case-analyze on the pair `(s.holding p, bestNew p)` that drives `daStep`'s decision for woman `p`. There are four cases, two of which (`old hold preserved` and `new free-man wins`) recur in mirrored form depending on whether `s.holding p` was `some h` or `none`. We extract those two arguments into the local helpers `preserve_hold` and `new_hold` and dispatch each of the four cases with a single line. Throughout, the key external lemmas are: * `pl_free_props` — anyone in `proposerList p` was free and proposed to `p`. * `daStep_nc_free` / `daStep_nc_held` — `nextChoice j` advances by 1 if `j` was free, stays put otherwise. * `not_isFree_iff` — `j` is not free in `s` iff some woman holds `j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- `HoldInv` is preserved by one DA step. Proof structure: case-analyze on the pair `(s.holding p, bestNew p)` that drives `daStep`'s decision for woman `p`. There are four cases, two of which (`old hold preserved` and `new free-man wins`) recur in mirrored form depending on whether `s.holding p` was `some h` or `none`. We extract those two arguments into the local helpers `preserve_hold` and `new_hold` and dispatch each of the four cases with a single line. Throughout, the key external lemmas are: * `pl_free_props` — anyone in `proposerList p` was free and proposed to `p`. * `daStep_nc_free` / `daStep_nc_held` — `nextChoice j` advances by 1 if `j` was free, stays put otherwise. * `not_isFree_iff` — `j` is not free in `s` iff some woman holds `j`. -/
lemma holdinv_step (w m : Preferences n) (s : DAState n)
    (hhold : HoldInv m s) : HoldInv m (daStep w m s) := by
  intro j p hp
  -- Fold `(daStep w m s).holding p` to the canonical `match` form (see
  -- `daStep_holding`). This is what lets us name `pl` / `bn` afterwards
  -- without losing the connection to `hp`.
  rw [daStep_holding] at hp
  -- Names matching the inner `let`s of `daStep`.
  set pl : Fin n → List (Fin n) := fun p' =>
    (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p'))).val.toList with pl_def
  set bn : Fin n → Option (Fin n) := fun p' =>
    (pl p').argmin (fun k => (w.prefs p').idxOf k) with bn_def
  -- `(s.holding p, bn p)` is exactly what `daStep_holding` matches on.
  change (match s.holding p, bn p with
    | none,   none   => none
    | some h, none   => some h
    | none,   some q => some q
    | some h, some q =>
        if (w.prefs p).idxOf q < (w.prefs p).idxOf h then some q else some h) = some j at hp
  ----------------------------------------------------------------------------
  -- Reusable closer 1: woman `p`'s old hold `h` survives the step (because
  -- no new proposer outranks him). Then `h = j` and `j`'s cursor doesn't
  -- advance (since `j` is not free in `s` — woman `p` holds him).
  ----------------------------------------------------------------------------
  have preserve_hold : ∀ {h : Fin n}, h = j → s.holding p = some h →
      p ∈ (m.prefs j).take ((daStep w m s).nextChoice j) := by
    rintro h rfl hs
    -- `rfl` here substitutes `j := h`, so the conclusion is in terms of `h`.
    have hh_not_free : isFree s h = false := (not_isFree_iff s h).mpr ⟨p, hs⟩
    rw [daStep_nc_held hh_not_free]
    exact hhold h p hs
  ----------------------------------------------------------------------------
  -- Reusable closer 2: a free man `q ∈ proposerList p` becomes (or is) `p`'s
  -- holder. Then `q = j`, his cursor advances by 1 in `daStep`, and `p` sits
  -- at index `s.nextChoice q` of `m.prefs q` — so `p` is now within the
  -- *new* `take` window.
  ----------------------------------------------------------------------------
  have new_hold : ∀ {q : Fin n}, q = j → q ∈ pl p →
      p ∈ (m.prefs j).take ((daStep w m s).nextChoice j) := by
    rintro q rfl hq_in
    -- Substitution: `j := q`. Conclusion is in terms of `q`.
    have ⟨hfq, hptq⟩ := pl_free_props s m p q hq_in
    -- `propTarget m q (s.nextChoice q) = some p`, i.e.
    -- `(m.prefs q)[s.nextChoice q]? = some p`. Unpack via `getElem?_eq_some_iff`.
    obtain ⟨hq_lt_len, hget⟩ : ∃ h, (m.prefs q)[s.nextChoice q]'h = p :=
      List.getElem?_eq_some_iff.mp hptq
    -- After the step, `q`'s cursor is `s.nextChoice q + 1`; `p` sits at index
    -- `s.nextChoice q < s.nextChoice q + 1`, so `p` is inside the new prefix.
    rw [daStep_nc_free hfq, List.mem_take_iff_idxOf_lt]
    · -- `(m.prefs q).idxOf p < s.nextChoice q + 1`
      rw [← hget, (m.valid q).1.idxOf_getElem _ hq_lt_len]
      omega
    · exact pref_list_mem _ (m.valid q).1 (m.valid q).2 p
  ----------------------------------------------------------------------------
  -- Main case split — four cases, each one liner.
  ----------------------------------------------------------------------------
  cases hs : s.holding p with
  | none =>
      cases hb : bn p with
      | none =>
          -- (none, none): match returns `none`, contradicting `hp : … = some j`.
          rw [hs, hb] at hp; exact absurd hp (by simp)
      | some q =>
          -- (none, some q): new proposer `q` takes the slot; `q = j`.
          rw [hs, hb] at hp
          exact new_hold (Option.some.inj hp) (List.argmin_mem hb)
  | some h =>
      cases hb : bn p with
      | none =>
          -- (some h, none): old hold kept; `h = j`.
          rw [hs, hb] at hp
          exact preserve_hold (Option.some.inj hp) hs
      | some q =>
          -- (some h, some q): outcome depends on whether `q` outranks `h`.
          rw [hs, hb] at hp
          -- The match reduces definitionally to an `if`; force the reduction so
          -- `split_ifs` can see the conditional.
          dsimp only at hp
          split_ifs at hp with hlt
          · -- `q` upgrades: same as Case 2 above.
            exact new_hold (Option.some.inj hp) (List.argmin_mem hb)
          · -- `h` stays: same as Case 3 above.
            exact preserve_hold (Option.some.inj hp) hs
