import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ApxParadox

/-!
# apx_search

Topic: social_choice   Node: 914a3af6ff99

Pruned search over candidate seat vectors for a list of profiles; succeeds iff every complete assignment contains a population paradox.
-/

/-- Pruned search: assign each pending profile one of its candidate seat vectors; a branch is closed as soon as the new assignment forms a population paradox with an earlier one. Returns `true` iff every complete branch is closed. -/
def apx_search (done : List ((Fin 4 → ℕ) × (Fin 4 → ℕ)))
    (todo : List ((Fin 4 → ℕ) × List (Fin 4 → ℕ))) : Bool :=
  match todo with
  | [] => false
  | (p, cs) :: rest => cs.all fun a =>
      (done.any fun x => apx_paradox x.1 x.2 p a || apx_paradox p a x.1 x.2) ||
        apx_search ((p, a) :: done) rest
