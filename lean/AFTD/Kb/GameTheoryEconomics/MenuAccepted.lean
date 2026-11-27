import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DelegationMenu

/-!
# menu_accepted

Topic: mechanism_design   Node: bbbbc2c5efa5

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.2

For a delegation menu M on type E, a family of feasible sets F : Set (Finset E), and principal values x : E → ℝ, the accepted reports are the nonempty sets S ∈ F that satisfy M.accepts S x.
-/

/-- The family of nonempty feasible reports accepted by a menu M at principal value realization x. -/
def menu_accepted {E : Type*} (M : DelegationMenu E) (F : Set (Finset E)) (x : E → ℝ) : Set (Finset E) := {S ∈ F | S.Nonempty ∧ M.accepts S x}
