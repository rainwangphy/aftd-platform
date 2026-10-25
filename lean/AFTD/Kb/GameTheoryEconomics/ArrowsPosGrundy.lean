import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos
import AFTD.Kb.GameTheoryEconomics.ArrowsLegalMove
import AFTD.Kb.GameTheoryEconomics.NatMexSet

/-!
# arrows_pos_grundy

Topic: combinatorial_games   Node: ac5f88d44001

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

The Grundy value of a position p : ArrowsPos V in the Game of Arrows on G at recursion depth fuel, defined as 0 when fuel = 0 and as the minimum excluded natural number (nat_mex_set) of the values of legal moves q at depth fuel' when fuel = fuel' + 1.
-/

/-- The Grundy value of a Game of Arrows position p under fuel recursion, using the minimum excluded value over all legal moves. -/
noncomputable def arrows_pos_grundy {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (fuel : ℕ) (p : ArrowsPos V) : ℕ := match fuel with
  | 0 => 0
  | fuel + 1 => nat_mex_set { n : ℕ | ∃ q, ArrowsLegalMove G p q ∧ n = arrows_pos_grundy G fuel q }
