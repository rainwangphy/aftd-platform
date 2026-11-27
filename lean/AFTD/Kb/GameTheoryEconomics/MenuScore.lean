import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DelegationMenu
import AFTD.Kb.GameTheoryEconomics.IsMaximalAccepted

/-!
# menu_score

Topic: mechanism_design   Node: 7962e5203c28

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.2

The score of a delegation menu M at principal values x with feasible family F is the infimum in ℝ of the values ∑ i ∈ S, x i over all sets S that are inclusion-maximal in menu_accepted M F x.
-/

/-- The score of a delegation menu at a principal value realization: the infimum principal value of inclusion-maximal accepted reports. -/
noncomputable def menu_score {E : Type*} [DecidableEq E]
    (M : DelegationMenu E) (F : Set (Finset E)) (x : E → ℝ) : ℝ := sInf {r : ℝ | ∃ S, is_maximal_accepted M F x S ∧ r = ∑ i ∈ S, x i}
