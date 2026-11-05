import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EpsteinRemotenessLevel

/-!
# epstein_remoteness

Topic: combinatorial_games   Node: 2aa15608ecc1

Provenance: formalization of a published result. Source: arXiv:2611.05898 Def 1.2

The remoteness epstein_remoteness n of position n in Epstein's game, defined as the least natural number k such that n ∈ epstein_remoteness_level k, or ⊤ if no such k exists.
-/

/-- The remoteness function R(n) in Epstein's put-or-take-a-square game, valued in WithTop ℕ. -/
noncomputable def epstein_remoteness (n : ℕ) : WithTop ℕ :=
  open Classical in
  if h : ∃ k : ℕ, n ∈ epstein_remoteness_level k then
    some (Nat.find h)
  else
    ⊤
