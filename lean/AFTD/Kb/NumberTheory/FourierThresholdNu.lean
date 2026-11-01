import AFTD.Prelude

/-!
# fourier_threshold_nu

Topic: elementary_number_theory   Node: 5ed5b6249c31

Provenance: formalization of a published result. Source: arXiv:2610.38447, Section 4, eq. (28)

The Fourier threshold nu(d) is the minimum size of the Fourier support of a function f from (ZMod 2)^d to ZMod 3 whose zero set is precisely {0}.
-/

/-- The extremal Fourier threshold nu(d) is the minimum Fourier support size of an F_3-valued function on F_2^d with unique zero at the origin. -/
def fourier_threshold_nu (d : ℕ) : ℕ :=
  (Finset.filter (fun f : (Fin d → ZMod 2) → ZMod 3 => ∀ x, (f x = 0 ↔ x = 0)) Finset.univ).fold
    min (2^d + 1) (fun f => (Finset.filter (fun (u : Fin d → ZMod 2) =>
      (-1 : ZMod 3)^d * ∑ x : Fin d → ZMod 2, f x * (if ∑ i, u i * x i = 0 then 1 else -1) ≠ 0) Finset.univ).card)
