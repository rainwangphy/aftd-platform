import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DeterministicMenu

/-!
# accepted_reports

Topic: mechanism_design   Node: bac26a20ac12

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.2

Given a family of finite sets F : Set (Finset E), a deterministic menu M : deterministic_menu E, and principal values x : E → ℝ, the accepted reports are the nonempty finite sets S in F such that the pair ⟨S, x|_S⟩ belongs to M.
-/

/-- The set of nonempty finite reports in F accepted by a deterministic menu at principal realization x. -/
def accepted_reports {E : Type*} (F : Set (Finset E)) (M : deterministic_menu E) (x : E → ℝ) : Set (Finset E) := {S ∈ F | S.Nonempty ∧ (⟨S, fun (i : S) => x i.val⟩ : (S : Finset E) × (S → ℝ)) ∈ M}
