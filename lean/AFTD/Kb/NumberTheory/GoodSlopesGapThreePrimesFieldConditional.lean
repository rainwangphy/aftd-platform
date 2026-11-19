import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesGapThreePrimesConditional
import AFTD.Kb.NumberTheory.GoodSlopesUnitCoverSquarefree
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm

/-!
# good_slopes_gap_three_primes_field_conditional

Topic: elementary_number_theory   Node: 1cde71ae0d8a

Provenance: original. Related work: The general gap question is Question 10.2 of https://arxiv.org/abs/2611.04551; the assumed prime-field direction bound follows from Theorem 1.1 of https://arxiv.org/abs/2212.12823.

Let p and q be primes with p at least 5, q at least 2p−1, and 3(p+1)<2q. Suppose for each r in {p,q} that every set of r points over the r-element field with at least (r+1)/2 injective finite directions is a line. Then every non-extremal permutation modulo 3pq has at most 2(p−1)(q−2) good slopes.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_gap_three_primes_field_conditional (p q : ℕ)
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hp : 5 ≤ p) (hsep : 2*p-1 ≤ q)
    (hsize : (p+1)*3 < 2*q) (hdirP : (∀ T : Finset (ZMod p × ZMod p), T.card = p →
      (∃ G : Finset (ZMod p), (p+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : ZMod p × ZMod p => z.2 + a*z.1) T) →
      (∃ x : ZMod p, ∀ z ∈ T, z.1 = x) ∨ (∃ a t : ZMod p, ∀ z ∈ T, z.2 + a*z.1 = t))) (hdirQ : (∀ T : Finset (ZMod q × ZMod q), T.card = q →
      (∃ G : Finset (ZMod q), (q+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : ZMod q × ZMod q => z.2 + a*z.1) T) →
      (∃ x : ZMod q, ∀ z ∈ T, z.1 = x) ∨ (∃ a t : ZMod q, ∀ z ∈ T, z.2 + a*z.1 = t)))
    (f : Equiv.Perm (ZMod (3*(p*q)))) (hf : ¬ is_extremal_perm (3*(p*q)) f)
    :
    (good_slopes (3*(p*q)) f).card ≤ 2*(p-1)*(q-2) := by
  classical
  have hppr : Nat.Prime p := Fact.out
  have hqpr : Nat.Prime q := Fact.out
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hppr hqpr).mpr (by omega)
  have hcop3p : Nat.Coprime 3 p := (Nat.coprime_primes (by decide) hppr).mpr (by omega)
  have hcop3q : Nat.Coprime 3 q := (Nat.coprime_primes (by decide) hqpr).mpr (by omega)
  have hcop3 : Nat.Coprime 3 (p*q) := hcop3p.mul_right hcop3q
  have hpq : Squarefree (p*q) := (Nat.squarefree_mul hcop).mpr ⟨hppr.squarefree,hqpr.squarefree⟩
  have h3 : Nat.Prime 3 := by decide
  have hsq : Squarefree (3*(p*q)) := (Nat.squarefree_mul hcop3).mpr ⟨h3.squarefree,hpq⟩
  obtain ⟨c,_,hc⟩ := good_slopes_unit_cover_squarefree (3*(p*q)) hsq f
  exact good_slopes_gap_three_primes_conditional p q hp hsep hsize hdirP hdirQ f hf ⟨c,hc⟩
