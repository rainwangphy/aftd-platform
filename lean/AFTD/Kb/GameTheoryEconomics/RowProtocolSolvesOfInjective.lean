import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowView
import AFTD.Kb.GameTheoryEconomics.RowViewOfSage
import AFTD.Kb.GameTheoryEconomics.RowProtocolSolves
import AFTD.Kb.GameTheoryEconomics.RowLocalView
import AFTD.Kb.GameTheoryEconomics.RowMultiset

/-!
# row_protocol_solves_of_injective

Topic: combinatorial_games   Node: 588e7f7e5ccd

Provenance: helper lemma. step towards sages_row_upper_bound_binomial

If a protocol with announcements in α solves the row puzzle, then composing it with any injective map α → β gives a protocol with announcements in β that still solves it.
-/

/-- Injectivity of the announcement map is enough to turn a solving protocol into a solving protocol over a larger alphabet. -/
theorem row_protocol_solves_of_injective {S : ℕ} {α β : Type*} (hS : 2 ≤ S)
    (f : α → β) (hf : Function.Injective f) (p : RowLocalView (Fin S) → α)
    (hp : RowProtocolSolves S hS p) :
    RowProtocolSolves S hS (fun v => f (p v)) := by
  intro x π₁ π₂ hview hmulti
  apply hp x π₁ π₂ hview
  have hmap (π : Equiv.Perm (Fin S)) :
      rowMultiset hS (fun v => f (p v)) π =
      Multiset.map f (rowMultiset hS p π) := by
    dsimp [rowMultiset]
    rw [Multiset.map_map]
    rfl
  apply Multiset.map_injective hf
  rwa [← hmap, ← hmap]
