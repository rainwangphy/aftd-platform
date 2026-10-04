import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DaWomanKKnownSafelyManipulable
import AFTD.Kb.GameTheoryEconomics.WomanWeaklyPrefers
import AFTD.Kb.GameTheoryEconomics.DeferredAcceptance
import AFTD.Kb.GameTheoryEconomics.WomanStrictlyPrefers

/-!
# da_three_by_three_three_known_safely_manipulable

Topic: matching_markets   Node: 556b7c01aedc

In the 3x3 market with complete rankings, a woman who knows three agents can safely and profitably manipulate men-proposing deferred acceptance: woman 0 (true m0 > m1 > m2) knows woman 1 (m1 > m0), man 0 (w1 > w0) and man 1 (w0 > w1), and swaps m1 and m2. So the RAT-degree of deferred acceptance without truncation is at most 3 in this market, refuting the conjecture of arXiv:2502.18805 (Sec. 8.1) that 5 is tight.
-/

/-- In the 3-man, 3-woman market with complete rankings, three known agents already let a woman manipulate men-proposing deferred acceptance safely and profitably: woman 0 (true ranking m0 > m1 > m2) knows woman 1 (m1 > m0 > ...), man 0 (w1 > w0 > ...) and man 1 (w0 > w1 > ...), and swaps m1 and m2. So the RAT-degree of deferred acceptance without truncation is at most 3 here, not 5: the conjecture of arXiv:2502.18805 (Sec. 8.1) that 5 is tight fails in this market, where 5 is all the other agents. -/
theorem da_three_by_three_three_known_safely_manipulable :
    da_woman_k_known_safely_manipulable 3 3 3 := by
  let km : Fin 3 → Fin 3 → Fin 3 := ![![1, 0, 2], ![0, 1, 2], ![0, 1, 2]]
  let kw : Fin 3 → Fin 3 → Fin 3 := ![![0, 1, 2], ![1, 0, 2], ![0, 1, 2]]
  let T : Fin 3 → Fin 3 := ![0, 1, 2]
  let P : Fin 3 → Fin 3 := ![0, 2, 1]
  -- the outcome only depends on the unknown man 2 and woman 2
  have key : ∀ a : Fin 3 → Fin 3, Function.Injective a → ∀ b : Fin 3 → Fin 3, Function.Injective b →
      woman_weakly_prefers T
        (deferred_acceptance ![km 0, km 1, a] (Function.update ![T, kw 1, b] 0 P) 0)
        (deferred_acceptance ![km 0, km 1, a] (Function.update ![T, kw 1, b] 0 T) 0) := by
    unfold woman_weakly_prefers
    decide +kernel
  refine ⟨0, {0, 1}, {1}, by decide, by decide, km, kw, T, P, by decide, by decide, by decide,
    by decide, ?_, ?_⟩
  · intro rm rw hrm hrw hKm hKw
    have e1 : rm = ![km 0, km 1, rm 2] := by
      funext m; fin_cases m
      · exact hKm 0 (by decide)
      · exact hKm 1 (by decide)
      · rfl
    have e2 : ∀ X, Function.update rw 0 X = Function.update ![T, kw 1, rw 2] 0 X := by
      intro X; funext w; fin_cases w
      · simp
      · simp [hKw 1 (by decide)]
      · simp
    rw [e1, e2, e2]
    exact key _ (hrm 2) _ (hrw 2)
  · refine ⟨km, kw, by decide, by decide, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    unfold woman_strictly_prefers
    decide +kernel
