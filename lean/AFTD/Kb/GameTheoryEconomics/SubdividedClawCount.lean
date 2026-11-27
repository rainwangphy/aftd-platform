import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SubdividedClaw

/-!
# subdivided_claw_count

Topic: combinatorial_games   Node: 9af3e512eb6f

Provenance: formalization of a published result. Source: arXiv:2611.32746: The majority game chromatic number for dense random graphs

The number of connected components of a finite graph F whose induced subgraph is isomorphic to the once-subdivided claw.
-/

open Classical in
/-- The number of connected components isomorphic to the once-subdivided claw. -/
noncomputable def subdivided_claw_count {V : Type*} [Fintype V] (F : SimpleGraph V) : ℕ := (Finset.filter (fun c : F.ConnectedComponent => Nonempty (F.induce c.supp ≃g subdivided_claw)) Finset.univ).card
