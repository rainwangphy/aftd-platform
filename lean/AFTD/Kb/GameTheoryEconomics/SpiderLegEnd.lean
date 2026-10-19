import AFTD.Prelude

/-!
# SpiderLegEnd

Topic: combinatorial_games   Node: d9770097a047

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Section 6.1

The end condition of an attached leg in a spider state is either free (no arc on the leg), inward (pointing towards the centre), or outward (pointing away from the centre).
-/

/-- End condition of an attached leg in a spider state: free (no arc), inward, or outward. -/
inductive SpiderLegEnd : Type | free : SpiderLegEnd
  | inward : SpiderLegEnd
  | outward : SpiderLegEnd
  deriving DecidableEq, Repr
