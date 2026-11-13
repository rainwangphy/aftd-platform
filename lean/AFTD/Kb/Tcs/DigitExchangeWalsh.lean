import AFTD.Prelude

/-!
# digit_exchange_walsh

Topic: cryptography   Node: 1daca14b80da

Provenance: original. Related work: arXiv:2611.02572

Given a natural number m, an element c in GaloisField 2 m, input masks u, v in GaloisField 2 m, and output masks s, t in GaloisField 2 m, the binary Walsh transform digit_exchange_walsh m c u v s t is the sum over a, b in GaloisField 2 m of (-1)^(Tr(u * a + v * b + s * L + t * D(L) * a)), where D(x) = x^2 + x + c, L = D(a) * b, and Tr is the absolute trace to ZMod 2.
-/

/-- Binary Walsh transform W(u,v;s,t) of the digit-exchange permutation over GF(2^m). -/
noncomputable def digit_exchange_walsh (m : ℕ) (c : GaloisField 2 m) (u v s t : GaloisField 2 m) : ℤ := by
  classical
  let D (x : GaloisField 2 m) : GaloisField 2 m := x ^ 2 + x + c
  let F := GaloisField 2 m
  haveI : Fintype F := Fintype.ofFinite F
  exact ∑ a : F, ∑ b : F,
    let L := D a * b
    let val := u * a + v * b + s * L + t * D L * a
    if Algebra.trace (ZMod 2) F val = 0 then (1 : ℤ) else (-1 : ℤ)
