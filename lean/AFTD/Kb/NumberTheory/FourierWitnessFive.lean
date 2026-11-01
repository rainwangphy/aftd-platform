import AFTD.Prelude
import AFTD.Kb.NumberTheory.FourierThresholdNu

/-!
# fourier_witness_five

Topic: elementary_number_theory   Node: 6543d133b093

Provenance: helper lemma. step towards fourier_threshold_nu_odd_le_arithmetic_bound

The explicit test function f : (ZMod 2)^5 → ZMod 3 obtained by Fourier inversion from the dual combination with support the Hamming-weight classes {0,1,4} (coefficient 1 at u = 0, −1 elsewhere).
-/

/-- Explicit weight-symmetric Fourier witness in dimension 5: supports {0,1,4} in Hamming weight, +1 on u = 0 and −1 elsewhere. -/
def fourier_witness_five : (Fin 5 → ZMod 2) → ZMod 3 := fun x => (-1 : ZMod 3) ^ 5 *
    ∑ u ∈ Finset.univ.filter (fun u : Fin 5 → ZMod 2 =>
        (Finset.univ.filter (fun i : Fin 5 => u i ≠ 0)).card = 0 ∨
        (Finset.univ.filter (fun i : Fin 5 => u i ≠ 0)).card = 1 ∨
        (Finset.univ.filter (fun i : Fin 5 => u i ≠ 0)).card = 4),
      (if u = 0 then (1 : ZMod 3) else -1) * (if ∑ i, u i * x i = 0 then 1 else -1)
