import AFTD.Prelude

/-!
# good_slopes_prime7_five_on_line

Topic: elementary_number_theory   Node: fb76a02bcc47

Provenance: helper lemma. Elementary prime-field line-counting step for the 35-point fiber route to OP-1027.

Let S be a finite set of points over the field with seven elements. If it contains a point off y+x=0 and three distinct directions chosen from 2, 3, 4, 5, 6 are injective on S, then at most four points of S lie on y+x=0.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 15000000

private def form7x (a : ZMod 7) (p : ZMod 7 × ZMod 7) : ZMod 7 := p.2 + a * p.1

private def diagCandidates7 (A : Finset (ZMod 7)) (p : ZMod 7 × ZMod 7) : Finset (ZMod 7 × ZMod 7) :=
  Finset.univ.filter fun q => q.2 + q.1 = 0 ∧ (A.filter fun a => form7x a p = form7x a q).card = 0

private theorem prime7_line_table : ∀ (p : ZMod 7 × ZMod 7) (A : Finset (ZMod 7)),
    p.2 + p.1 ≠ 0 → A ⊆ ({2,3,4,5,6} : Finset (ZMod 7)) → A.card = 3 →
    (diagCandidates7 A p).card ≤ 4 := by decide

theorem good_slopes_prime7_five_on_line (S : Finset (ZMod 7 × ZMod 7))
    (A : Finset (ZMod 7)) (hA : A ⊆ ({2,3,4,5,6} : Finset (ZMod 7)))
    (hAc : A.card = 3) (hinj : ∀ a ∈ A, Set.InjOn (fun p : ZMod 7 × ZMod 7 => p.2 + a * p.1) S)
    (p : ZMod 7 × ZMod 7) (hp : p ∈ S) (hpbad : p.2 + p.1 ≠ 0) :
    (S.filter fun q => q.2 + q.1 = 0).card ≤ 4 := by
  classical
  have hsub : (S.filter fun q => q.2 + q.1 = 0) ⊆ diagCandidates7 A p := by
    intro q hq
    have ⟨hqS,hqdiag⟩ := Finset.mem_filter.mp hq
    simp only [diagCandidates7, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hqdiag, ?_⟩
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha heq
    have hpq : p = q := hinj a ha hp hqS heq
    subst p
    exact hpbad hqdiag
  exact (Finset.card_le_card hsub).trans (prime7_line_table p A hpbad hA hAc)
