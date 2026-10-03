import AFTD.Prelude

/-!
# apx_all_vectors

Topic: social_choice   Node: dceffbceb806

All seat vectors for four states with at most 8 seats each.
-/

/-- All seat vectors for four states with at most 8 seats each. -/
def apx_all_vectors : List (Fin 4 → ℕ) :=
  (List.range 9).flatMap fun a => (List.range 9).flatMap fun b =>
    (List.range 9).flatMap fun c => (List.range 9).map fun d => ![a, b, c, d]
