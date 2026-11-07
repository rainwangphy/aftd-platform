import AFTD.Prelude
import AFTD.Kb.Tcs.StandardYoungTableau
import AFTD.Kb.Tcs.RowColLe

/-!
# instFintypeStandardYoungTableau

Topic: combinatorics   Node: b7f87715fe33

Provenance: original. Related work: folklore

The type StandardYoungTableau D of standard Young tableaux on a finite diagram D is finite.
-/

/-- Fintype instance for standard Young tableaux on a finite diagram D. -/
noncomputable instance instFintypeStandardYoungTableau (D : Finset (ℕ × ℕ)) : Fintype (StandardYoungTableau D) := Fintype.ofInjective (fun T => T.toEquiv) (fun T₁ T₂ h => by cases T₁; cases T₂; cases h; rfl)
