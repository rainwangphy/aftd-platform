import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm
import AFTD.Kb.NumberTheory.GoodSlopesGapThreeCoprimeFromFiberBounds
import AFTD.Kb.Tcs.GoodSlopesProductUncoloredGapConditional
import AFTD.Kb.Tcs.GoodSlopesProductThreeColorGapConditional
import AFTD.Kb.NumberTheory.GoodSlopesUncoloredProductGapCrtConditional
import AFTD.Kb.NumberTheory.GoodSlopesColoredProductGapCrtConditional
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_gap_three_primes_conditional

Topic: elementary_number_theory   Node: c53a56269709

Provenance: helper lemma. Conditional general reduction for OP-1027. Compare the already-covered large-q range in arXiv:2611.04551 Theorem 9.3.

For primes 5≤p and q≥2p−1 with 3(p+1)<2q, the conjectured gap for a nonextremal permutation modulo 3pq follows from the two finite-field direction classifications and the unit-cover normalization.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
private lemma in962_units_totient (n : ℕ) [NeZero n] :
    ((Finset.univ : Finset (ZMod n)).filter fun b => IsUnit b).card = Nat.totient n := by
  classical
  rw [← ZMod.card_units_eq_totient]
  have e1 := ZMod.unitsEquivCoprime (n := n)
  have e2 : { x : ZMod n // Nat.Coprime x.val n } ≃ { x : ZMod n // IsUnit x } := by
    refine Equiv.subtypeEquivRight (fun x => ?_)
    have h := ZMod.isUnit_iff_coprime x.val n
    rw [ZMod.natCast_zmod_val] at h
    exact h.symm
  rw [Fintype.card_congr (e1.trans e2)]
  exact (Fintype.card_subtype (fun b : ZMod n => IsUnit b)).symm

theorem good_slopes_gap_three_primes_conditional (p q : ℕ)
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hp : 5 ≤ p) (hsep : 2*p-1 ≤ q)
    (hsize : (p+1)*3 < 2*q) (hdirP : (∀ T : Finset (ZMod p × ZMod p), T.card = p →
      (∃ G : Finset (ZMod p), (p+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : ZMod p × ZMod p => z.2 + a*z.1) T) →
      (∃ x : ZMod p, ∀ z ∈ T, z.1 = x) ∨ (∃ a t : ZMod p, ∀ z ∈ T, z.2 + a*z.1 = t))) (hdirQ : (∀ T : Finset (ZMod q × ZMod q), T.card = q →
      (∃ G : Finset (ZMod q), (q+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : ZMod q × ZMod q => z.2 + a*z.1) T) →
      (∃ x : ZMod q, ∀ z ∈ T, z.1 = x) ∨ (∃ a t : ZMod q, ∀ z ∈ T, z.2 + a*z.1 = t)))
    (f : Equiv.Perm (ZMod (3*(p*q)))) (hf : ¬ is_extremal_perm (3*(p*q)) f)
    (hcover : ∃ c : ZMod (3*(p*q)), ∀ m ∈ good_slopes (3*(p*q)) f, IsUnit (m+c)) :
    (good_slopes (3*(p*q)) f).card ≤ 2*(p-1)*(q-2) := by
  classical
  have hppr : Nat.Prime p := Fact.out
  have hqpr : Nat.Prime q := Fact.out
  have hpq : p < q := by omega
  have hpodd : p % 2 = 1 := hppr.eq_two_or_odd.resolve_left (by omega)
  have hqodd : q % 2 = 1 := hqpr.eq_two_or_odd.resolve_left (by omega)
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hppr hqpr).mpr (by omega)
  have hcop3p : Nat.Coprime 3 p := (Nat.coprime_primes (by decide) hppr).mpr (by omega)
  have hcop3q : Nat.Coprime 3 q := (Nat.coprime_primes (by decide) hqpr).mpr (by omega)
  have hcop3 : Nat.Coprime 3 (p*q) := hcop3p.mul_right hcop3q
  have hL : ((Finset.univ : Finset (ZMod (p*q))).filter fun b => IsUnit b).card = (p-1)*(q-1) := by
    rw [in962_units_totient,Nat.totient_mul hcop,Nat.totient_prime hppr,Nat.totient_prime hqpr]
  have hp1 : 0 < p-1 := by omega
  have hq3 : 2 < q-1 := by omega
  have hLd : 2*(p-1) < (p-1)*(q-1) := by
    have h := Nat.mul_lt_mul_of_pos_left hq3 hp1
    omega
  have h := good_slopes_gap_three_coprime_from_fiber_bounds (p*q) ((p-1)*(q-1)) (p-1) hcop3 f hf hcover hL hp1 hLd
    (by
      intro S hs hb
      exact good_slopes_uncolored_product_gap_crt_conditional p q hcop hp hpodd hqodd hsep hdirQ S hs hb)
    (by
      intro S color hs hx hc hb
      exact good_slopes_colored_product_gap_crt_conditional p q hcop hp hpodd hqodd hsep hsize hdirP hdirQ S color hs hx hc hb)
  have hqsub : q-1=(q-2)+1 := by omega
  have hmul : (p-1)*(q-1) = (p-1)*(q-2)+(p-1) := by
    calc
      _ = (p-1)*((q-2)+1) := by rw [hqsub]
      _ = _ := by ring
  have heq : 2*((p-1)*(q-1))-2*(p-1) = 2*(p-1)*(q-2) := by
    have hr : 2*((p-1)*(q-1)) = 2*((p-1)*(q-2))+2*(p-1) := by rw [hmul]; ring
    have hright : 2*((p-1)*(q-2)) = 2*(p-1)*(q-2) := by ring
    omega
  rw [heq] at h
  exact h
