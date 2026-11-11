import AFTD.Prelude

/-!
# good_slopes_prime7_anchored_line

Topic: elementary_number_theory   Node: 4ca42c3c8fad

Provenance: helper lemma. Finite prime-plane direction lemma for the 35-point fiber route to OP-1027; compare arXiv:2611.01465, Lemma 4.7.

Let e be one of 2, 3, 4, 5, 6. A set of seven points over the field with seven elements that contains (0,0) and (1,6), and on which y+ax is injective for every a among 2, 3, 4, 5, 6 except e, lies on the line y+x=0.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 15000000

private def form7 (a : ZMod 7) (p : ZMod 7 × ZMod 7) : ZMod 7 := p.2 + a * p.1

private def compatible7 (e : ZMod 7) (p q : ZMod 7 × ZMod 7) : Prop :=
  ∀ a : ZMod 7, a ∈ ({2,3,4,5,6} : Finset (ZMod 7)) → a ≠ e →
    form7 a p = form7 a q → p = q

private instance (e : ZMod 7) (p q : ZMod 7 × ZMod 7) : Decidable (compatible7 e p q) := by
  unfold compatible7
  infer_instance

private def candidates7 (e : ZMod 7) (p : ZMod 7 × ZMod 7) : Finset (ZMod 7 × ZMod 7) :=
  Finset.univ.filter fun q => compatible7 e q (0,0) ∧ compatible7 e q (1,6) ∧ compatible7 e q p

private theorem prime7_candidate_table : ∀ (e : ZMod 7) (p : ZMod 7 × ZMod 7),
    e ∈ ({2,3,4,5,6} : Finset (ZMod 7)) → p.2 + p.1 ≠ 0 →
    compatible7 e p (0,0) → compatible7 e p (1,6) →
    (candidates7 e p).card ≤ 7 ∧
    ((candidates7 e p).card = 7 →
      (((candidates7 e p).product (candidates7 e p)).filter fun qr => ¬ compatible7 e qr.1 qr.2).Nonempty) := by decide

theorem good_slopes_prime7_anchored_line (S : Finset (ZMod 7 × ZMod 7)) (e : ZMod 7)
    (hcard : S.card = 7) (h0 : (0,0) ∈ S) (h1 : (1,6) ∈ S)
    (he : e ∈ ({2,3,4,5,6} : Finset (ZMod 7)))
    (hinj : ∀ a : ZMod 7, a ∈ ({2,3,4,5,6} : Finset (ZMod 7)) → a ≠ e →
      Set.InjOn (fun p : ZMod 7 × ZMod 7 => p.2 + a * p.1) S) : ∀ p ∈ S, p.2 + p.1 = 0 := by
  classical
  intro p hp
  by_contra hpbad
  have hp0 : compatible7 e p (0,0) := by
    intro a ha hne h
    exact hinj a ha hne hp h0 h
  have hp1 : compatible7 e p (1,6) := by
    intro a ha hne h
    exact hinj a ha hne hp h1 h
  have hsub : S ⊆ candidates7 e p := by
    intro q hq
    simp only [candidates7, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha hne h; exact hinj a ha hne hq h0 h
    · intro a ha hne h; exact hinj a ha hne hq h1 h
    · intro a ha hne h; exact hinj a ha hne hq hp h
  obtain ⟨hupper, hconflict⟩ := prime7_candidate_table e p he hpbad hp0 hp1
  have hc : (candidates7 e p).card = 7 := by
    have hle := Finset.card_le_card hsub
    omega
  have hEq : S = candidates7 e p := Finset.eq_of_subset_of_card_le hsub (by omega)
  obtain ⟨qr, hqr⟩ := hconflict hc
  have hh := Finset.mem_filter.mp hqr
  have hprod := Finset.mem_product.mp hh.1
  have hq : qr.1 ∈ S := by rw [hEq]; exact hprod.1
  have hr : qr.2 ∈ S := by rw [hEq]; exact hprod.2
  apply hh.2
  intro a ha hne h
  exact hinj a ha hne hq hr h
