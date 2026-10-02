import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqIte

/-!
# catch_up_best_attach_map_congr

Topic: combinatorial_games   Node: 3895fa80850c

If F and G agree on every element of a list l of natural numbers, then the best outcome of F over the attached elements of l's finset equals the best outcome of G over l.
-/

/-- `best` over the finset of `l` equals `best` over `l` for functions agreeing on `l`. -/
theorem catch_up_best_attach_map_congr (l : List ℕ) (F G : ℕ → CatchUpOutcome)
    (hFG : ∀ x ∈ l, F x = G x) :
    CatchUpOutcome.best (l.toFinset.attach.toList.map (fun x => F x.1)) =
      CatchUpOutcome.best (l.map G) := by
  have hm : ∀ o, o ∈ l.toFinset.attach.toList.map (fun x => F x.1) ↔ o ∈ l.map G := by
    intro o
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists,
      List.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hFG x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, hFG x hx⟩
  rw [catch_up_outcome_best_eq_ite, catch_up_outcome_best_eq_ite]
  simp only [hm]
