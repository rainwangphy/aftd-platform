import AFTD.Prelude

/-!
# central_observable_one

Topic: quantum   Node: ae29ea020327

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. III.1

Given m : ℕ and a family of m × m complex matrices M : Fin 2 → Fin 2 → Matrix (Fin m) (Fin m) ℂ, central_observable_one m M is the m × m complex matrix defined by the double sum ∑ s0 : Fin 2, ∑ s1 : Fin 2, (if s1 = 0 then (1 : ℂ) else (-1 : ℂ)) • M s0 s1.
-/

/-- The central observable corresponding to sign f_1. -/
def central_observable_one (m : ℕ) (M : Fin 2 → Fin 2 → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ := ∑ s0 : Fin 2, ∑ s1 : Fin 2, (if s1 = 0 then (1 : ℂ) else (-1 : ℂ)) • M s0 s1
