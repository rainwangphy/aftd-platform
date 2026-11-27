import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DelegationMenu
import AFTD.Kb.GameTheoryEconomics.MenuAccepted

/-!
# is_maximal_accepted

Topic: mechanism_design   Node: b21ac5ebd0e5

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.2

A finite set S is inclusion-maximal in the accepted reports of menu M at principal values x with feasible family F if S is in menu_accepted M F x and is maximal with respect to inclusion in that set.
-/

/-- Inclusion-maximality among accepted reports of a delegation menu. -/
def is_maximal_accepted {E : Type*} [DecidableEq E]
    (M : DelegationMenu E) (F : Set (Finset E)) (x : E → ℝ) (S : Finset E) : Prop := Maximal (· ∈ menu_accepted M F x) S
