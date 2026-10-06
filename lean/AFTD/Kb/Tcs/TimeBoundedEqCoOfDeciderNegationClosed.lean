import AFTD.Prelude
import AFTD.Kb.Tcs.TimeBounded
import AFTD.Kb.Tcs.CoClass
import AFTD.Kb.Tcs.DeciderClassEqCo

/-!
# time_bounded_eq_co_of_decider_negation_closed

Topic: complexity_basics   Node: a236acef0d50

Provenance: formalization of a published result. Source: standard textbook result (complexity theory: a time-bounded decider class closed under negation equals its complement class)

Let T be a time bound and suppose the family of deciders computable within T steps is closed under Boolean negation, i.e. for every f : List Γ → Bool computed in time T there is g computed in time T with g w = !f w. Then the time-bounded class C = TimeBounded Γ T equals its complement class CoClass C: for every language L, L is decidable in time T if and only if its complement is.
-/

/-- A time-bounded class whose deciders are closed under negation equals its own complement class. -/
theorem time_bounded_eq_co_of_decider_negation_closed {Γ : Type} {T : ℕ → ℕ}
    (hD : ∀ f : List Γ → Bool,
      (∃ M : Turing.TM2ComputableInTime (id : List Γ → List Γ) Computability.encodeBool f,
        ∀ n, M.time n ≤ T n) →
      ∃ M : Turing.TM2ComputableInTime (id : List Γ → List Γ) Computability.encodeBool
        (fun w => !f w), ∀ n, M.time n ≤ T n) :
    ∀ L : Language Γ, TimeBounded Γ T L ↔ CoClass (TimeBounded Γ T) L := by
  intro L
  exact decider_class_eq_co (α := Γ)
    (fun f : List Γ → Bool => ∃ M : Turing.TM2ComputableInTime (id : List Γ → List Γ)
      Computability.encodeBool f, ∀ n, M.time n ≤ T n) hD L
