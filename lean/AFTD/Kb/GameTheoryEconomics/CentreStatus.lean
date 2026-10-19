import AFTD.Prelude

/-!
# CentreStatus

Topic: combinatorial_games   Node: 6ce9647edcfb

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Definition 3.1 and Section 6.1

The status of the central vertex in a spider state: none (no marked arcs incident), incoming (at least one incoming arc), outgoing (at least one outgoing arc), or free (both incoming and outgoing arcs, or special).
-/

/-- Status of the centre vertex: none (unmarked), incoming, outgoing, or free. -/
inductive CentreStatus : Type | none : CentreStatus
  | incoming : CentreStatus
  | outgoing : CentreStatus
  | free : CentreStatus
  deriving DecidableEq, Repr
