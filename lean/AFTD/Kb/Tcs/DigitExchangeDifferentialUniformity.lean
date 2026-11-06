import AFTD.Prelude

/-!
# digit_exchange_differential_uniformity

Topic: cryptography   Node: 74093277b87c

Provenance: formalization of a published result. Source: arXiv:2611.02572, Section 1, Eq. (1)-(2) and Theorem 1.1

Given an arbitrary natural number m (without any positivity or nonzeroness assumption) and an element c in GaloisField 2 m, the differential uniformity digit_exchange_differential_uniformity m c is defined as the maximum over all pairs α ≠ (0, 0) and all pairs β of the number of solutions x in (GaloisField 2 m)^2 to sub (G (add x α)) (G x) = β, where D(t) = t^2 + t + c, G(x) = (L, D(L) * x.1) with L = D(x.1) * x.2, add x y = (x.1 + y.1, x.2 + y.2 + (x.1 * y.1)^(2^(m-1))), and sub y z = (y.1 + z.1, y.2 + z.1 + z.2 + (y.1 * z.1)^(2^(m-1))).
-/

/-- Differential uniformity of the digit-exchange permutation G_c on (Z/4Z)^m in Teichmüller digits over GaloisField 2 m. -/
noncomputable def digit_exchange_differential_uniformity (m : ℕ) (c : GaloisField 2 m) : ℕ := by
  classical
  let add (x y : GaloisField 2 m × GaloisField 2 m) : GaloisField 2 m × GaloisField 2 m :=
    (x.1 + y.1, x.2 + y.2 + (x.1 * y.1) ^ (2 ^ (m - 1)))
  let sub (y z : GaloisField 2 m × GaloisField 2 m) : GaloisField 2 m × GaloisField 2 m :=
    (y.1 + z.1, y.2 + z.1 + z.2 + (y.1 * z.1) ^ (2 ^ (m - 1)))
  let D (x : GaloisField 2 m) : GaloisField 2 m := x ^ 2 + x + c
  let G (x : GaloisField 2 m × GaloisField 2 m) : GaloisField 2 m × GaloisField 2 m :=
    let L := D x.1 * x.2
    (L, D L * x.1)
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite (GaloisField 2 m)
  exact Finset.sup (Finset.univ.filter (fun α : GaloisField 2 m × GaloisField 2 m => α ≠ (0, 0)))
    (fun α => Finset.sup Finset.univ (fun β =>
      Finset.card (Finset.filter (fun x => sub (G (add x α)) (G x) = β) Finset.univ)))
