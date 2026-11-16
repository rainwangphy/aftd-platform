import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsTwoThirdsConvex

Topic: general_equilibrium   Node: 44ac701fd468

Provenance: formalization of a published result. Source: arXiv:2611.16207, Core nonemptiness for 2/3-convex games, Definition 1

A transferable-utility game G with real characteristic function v on a finite set of players N is 2/3-convex if for every triple of distinct coalitions S₁, S₂, S₃ ⊆ N, at least two of the three pairs satisfy the supermodular inequality v(Sᵢ ∪ Sⱼ) + v(Sᵢ ∩ Sⱼ) ≥ v(Sᵢ) + v(Sⱼ).
-/

/-- A coalitional game is 2/3-convex if at least two of any three distinct coalitions satisfy the supermodular inequality. -/
def CoalitionalGame.IsTwoThirdsConvex {N : Type*} [DecidableEq N] (G : CoalitionalGame N ℝ) : Prop := ∀ (S₁ S₂ S₃ : Finset N), S₁ ≠ S₂ → S₁ ≠ S₃ → S₂ ≠ S₃ →
    (G.v (S₁ ∪ S₂) + G.v (S₁ ∩ S₂) ≥ G.v S₁ + G.v S₂ ∧
     G.v (S₁ ∪ S₃) + G.v (S₁ ∩ S₃) ≥ G.v S₁ + G.v S₃) ∨
    (G.v (S₁ ∪ S₂) + G.v (S₁ ∩ S₂) ≥ G.v S₁ + G.v S₂ ∧
     G.v (S₂ ∪ S₃) + G.v (S₂ ∩ S₃) ≥ G.v S₂ + G.v S₃) ∨
    (G.v (S₁ ∪ S₃) + G.v (S₁ ∩ S₃) ≥ G.v S₁ + G.v S₃ ∧
     G.v (S₂ ∪ S₃) + G.v (S₂ ∩ S₃) ≥ G.v S₂ + G.v S₃)
