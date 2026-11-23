import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation

/-!
# appearance_vector

Topic: social_choice   Node: a893ca36f941

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 7

The appearance vector of an individual z in a power relation r is the list whose k-th element is the number of coalitions in the k-th equivalence class of r that contain z.
-/

/-- Appearance vector of an individual in a power relation. -/
def appearance_vector {X : Type*} [DecidableEq X] (r : PowerRelation X) (z : X) : List ℕ := r.classes.map (fun c => (c.filter (fun S => z ∈ S)).card)
