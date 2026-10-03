import AFTD.Prelude

/-!
# apx_profiles

Topic: social_choice   Node: d160512c9612

The twelve four-state population profiles of the witness; state 2 always has population 30.
-/

/-- The twelve population profiles of the witness (state 2 always has population 30). -/
def apx_profiles : List (Fin 4 → ℕ) :=
  [![3, 2, 30, 5], ![3, 3, 30, 4], ![3, 3, 30, 12], ![3, 4, 30, 3], ![3, 5, 30, 2], ![3, 12, 30, 3],
   ![4, 2, 30, 12], ![4, 3, 30, 3], ![5, 2, 30, 3], ![12, 2, 30, 4], ![12, 3, 30, 3], ![12, 4, 30, 2]]
