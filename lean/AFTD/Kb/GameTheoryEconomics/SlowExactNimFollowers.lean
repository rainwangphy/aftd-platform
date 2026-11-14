import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimStep

/-!
# slow_exact_nim_followers

Topic: combinatorial_games   Node: f5f8d5fc422d

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 1

For natural numbers k and n and a position x : Fin n → ℕ, the finite set of legal followers slow_exact_nim_followers k n x is the set of positions in Fin n → ℕ obtained by applying slow_exact_nim_step x S for all subsets S : Finset (Fin n) of size k whose elements all satisfy 0 < x i.
-/

/-- The finite set of legal followers of a position in slow exact k-Nim on n piles. -/
def slow_exact_nim_followers (k n : ℕ) (x : Fin n → ℕ) : Finset (Fin n → ℕ) := ((Finset.powersetCard k (Finset.univ : Finset (Fin n))).filter (fun S => ∀ i ∈ S, 0 < x i)).image (slow_exact_nim_step x)
