import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.Tcs.G

/-!
# GS.stable_matching_perfect

Topic: matching_markets   Node: ed36032dbaed

Provenance: formalization of a published result. Source: EconCSLib, `GS.stable_matching_perfect`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/RuralHospitals.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In the balanced full-preference one-to-one market, every stable matching is **perfect**: every woman and every man is matched. This is the Rural-Hospitals specialization — the matched set is all of `Fin n` in every stable matching, hence invariant across the stable set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
/-- In the balanced full-preference one-to-one market, every stable matching is **perfect**: every woman and every man is matched. This is the Rural-Hospitals specialization — the matched set is all of `Fin n` in every stable matching, hence invariant across the stable set. -/
theorem GS.stable_matching_perfect
    (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) :
    (∀ i : Fin n, (μ.matchM i).isSome) ∧ (∀ j : Fin n, (μ.matchW j).isSome) := by
  -- Every woman is matched.
  have hwomen : ∀ i : Fin n, (μ.matchM i).isSome := by
    intro i₀
    by_contra hi0
    rw [Option.not_isSome_iff_eq_none] at hi0
    -- Some man is unmatched, else `matchW` is a total injection (hence a
    -- bijection) and would force `i₀` to be matched.
    obtain ⟨j₀, hj0⟩ : ∃ j : Fin n, μ.matchW j = none := by
      by_contra hall
      push Not at hall
      have hsome : ∀ j, (μ.matchW j).isSome := fun j =>
        Option.isSome_iff_ne_none.mpr (hall j)
      set f : Fin n → Fin n := fun j => (μ.matchW j).get (hsome j) with hf
      have hf_spec : ∀ j, μ.matchW j = some (f j) := fun j =>
        (Option.some_get (hsome j)).symm
      have hf_inj : Function.Injective f := by
        intro j1 j2 he
        have e1 := (μ.consistent (f j1) j1).mpr (hf_spec j1)
        have e2 := (μ.consistent (f j2) j2).mpr (hf_spec j2)
        rw [he] at e1; rw [e2] at e1
        exact (Option.some.inj e1).symm
      obtain ⟨j, hj⟩ := (Finite.injective_iff_bijective.mp hf_inj).2 i₀
      have hcon : μ.matchM i₀ = some j := (μ.consistent i₀ j).mpr (hj ▸ hf_spec j)
      rw [hi0] at hcon
      simp at hcon
    -- `(i₀, j₀)` blocks: both are unmatched and `some _ ≻ none`.
    exact hμ i₀ j₀ ⟨by rw [hi0]; exact ⟨trivial, not_false⟩,
                    by rw [hj0]; exact ⟨trivial, not_false⟩⟩
  -- Every man is matched (symmetric: `matchM` is now a total injection).
  refine ⟨hwomen, fun j₀ => ?_⟩
  by_contra hj0
  rw [Option.not_isSome_iff_eq_none] at hj0
  set g : Fin n → Fin n := fun i => (μ.matchM i).get (hwomen i) with hg
  have hg_spec : ∀ i, μ.matchM i = some (g i) := fun i =>
    (Option.some_get (hwomen i)).symm
  have hg_inj : Function.Injective g := by
    intro i1 i2 he
    have e1 := (μ.consistent i1 (g i1)).mp (hg_spec i1)
    have e2 := (μ.consistent i2 (g i2)).mp (hg_spec i2)
    rw [he] at e1; rw [e2] at e1
    exact (Option.some.inj e1).symm
  obtain ⟨i, hi⟩ := (Finite.injective_iff_bijective.mp hg_inj).2 j₀
  have hcon : μ.matchW j₀ = some i := (μ.consistent i j₀).mp (hi ▸ hg_spec i)
  rw [hj0] at hcon
  simp at hcon
