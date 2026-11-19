import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirectionsCrtTransfer
import AFTD.Kb.Tcs.GoodSlopesProductUncoloredGapConditional
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_uncolored_product_gap_crt_conditional

Topic: elementary_number_theory   Node: f98658540f04

Provenance: helper lemma. CRT transfer of the finite-field product bounds for OP-1027.

Under the stated prime, size and finite-field direction hypotheses, a set of pq points modulo pq with a bad unit direction has at most (p−1)(q−1)−(p−1) good unit directions.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_uncolored_product_gap_crt_conditional (p q : ℕ) [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hcop : Nat.Coprime p q) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) (hqodd : q % 2 = 1)
    (hsep : 2*p-1 ≤ q)
    (hdirQ : ∀ T : Finset (ZMod q × ZMod q), T.card = q →
      (∃ G : Finset (ZMod q), (q+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : ZMod q × ZMod q => z.2+a*z.1) T) →
      (∃ x : ZMod q, ∀ z ∈ T, z.1=x) ∨ (∃ a t : ZMod q, ∀ z ∈ T, z.2+a*z.1=t))
    (S : Finset (ZMod (p*q) × ZMod (p*q))) (hcard : S.card = p*q)
    (hbad : ∃ b : ZMod (p*q), IsUnit b ∧ b ∉ good_slopes_point_directions (p*q) S) :
    (good_slopes_point_directions (p*q) S).card ≤ (p-1)*(q-1)-(p-1) := by
  classical
  let e := ZMod.chineseRemainder hcop
  let E := Equiv.prodCongr e.toEquiv e.toEquiv
  let S' := S.image E
  have hS' : S'.card = p*q := by
    dsimp [S']
    rw [Finset.card_image_of_injective _ E.injective, hcard]
  let Good : Finset (ZMod p × ZMod q) := (Finset.univ : Finset (ZMod p × ZMod q)).filter fun ab =>
    ab.1 ≠ 0 ∧ ab.2 ≠ 0 ∧ Set.InjOn (fun z : ((ZMod p × ZMod q) × (ZMod p × ZMod q)) =>
      (z.2.1+ab.1*z.1.1,z.2.2+ab.2*z.1.2)) S'
  have hcrt (c : ZMod (p*q)) : c ∈ good_slopes_point_directions (p*q) S ↔
      (e c).1 ≠ 0 ∧ (e c).2 ≠ 0 ∧ Set.InjOn (fun z : ((ZMod p × ZMod q) × (ZMod p × ZMod q)) =>
        (z.2.1+(e c).1*z.1.1,z.2.2+(e c).2*z.1.2)) S' :=
    good_slopes_point_directions_crt_transfer p q hcop S c
  have hGood : Good = (good_slopes_point_directions (p*q) S).image e := by
    ext ab
    constructor
    · intro hab
      have hh := (Finset.mem_filter.mp hab).2
      refine Finset.mem_image.mpr ⟨e.symm ab, ?_,e.apply_symm_apply ab⟩
      apply (hcrt (e.symm ab)).mpr
      simpa only [e.apply_symm_apply] using hh
    · intro hab
      obtain ⟨c,hc0,rfl⟩ := Finset.mem_image.mp hab
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hcrt c).mp hc0⟩
  have hbad' : ∃ a : ZMod p, a ≠ 0 ∧ ∃ b : ZMod q, b ≠ 0 ∧
      ¬ Set.InjOn (fun z : ((ZMod p × ZMod q) × (ZMod p × ZMod q)) =>
        (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S' := by
    obtain ⟨c,hcu,hcbad⟩ := hbad
    have hu : IsUnit (e c) := (MulEquiv.isUnit_map e).mpr hcu
    have ⟨hu5,hu11⟩ := Prod.isUnit_iff.mp hu
    refine ⟨(e c).1,isUnit_iff_ne_zero.mp hu5,(e c).2,isUnit_iff_ne_zero.mp hu11, ?_⟩
    intro hh
    exact hcbad ((hcrt c).mpr ⟨isUnit_iff_ne_zero.mp hu5,isUnit_iff_ne_zero.mp hu11,hh⟩)
  have h := good_slopes_product_uncolored_gap_conditional (ZMod p) (ZMod q) p q
    (by simp) (by simp) hp5 hpodd hqodd hsep hdirQ S' hS' hbad'
  change Good.card ≤ (p-1)*(q-1)-(p-1) at h
  rw [hGood, Finset.card_image_of_injective _ e.injective] at h
  exact h
