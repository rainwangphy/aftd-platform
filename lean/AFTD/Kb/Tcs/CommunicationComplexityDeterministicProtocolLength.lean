import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.Deterministic.Protocol.length

Topic: communication   Node: 4002c4d913bf

Provenance: formalization of a published result. Source: arXiv:2611.11488 Section 5.2, page 19

For a deterministic two-party protocol p and inputs x and y, the transcript length p.length x y is the number of bits communicated by the parties on input (x, y).
-/

/-- The transcript length of a deterministic protocol on a given pair of inputs. -/
def CommunicationComplexity.Deterministic.Protocol.length {X Y α : Type*} :
    CommunicationComplexity.Deterministic.Protocol X Y α → X → Y → ℕ := fun p x y => match p with
  | .output _ => 0
  | .alice f k => 1 + length (k (f x)) x y
  | .bob g k => 1 + length (k (g y)) x y
