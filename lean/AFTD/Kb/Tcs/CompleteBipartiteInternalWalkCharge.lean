import AFTD.Prelude

/-!
# complete_bipartite_internal_walk_charge

Topic: graphs   Node: 36c05bc2221e

Provenance: helper lemma. OP-1957 saturated-twin bridge-family walk count; scratch Lean axiom audit completed.

A complete bipartite configuration gives a lower bound on the internal degree charge.
-/

theorem complete_bipartite_internal_walk_charge
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S A B : Finset V) (hA : A ⊆ S) (hB : B ⊆ S) (hdis : Disjoint A B)
    (hAcard : A.card=4) (hcross : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) :
    4*B.card*(B.card-1)+12*B.card ≤
      Finset.sum S (fun q => ((H.neighborFinset q) ∩ S).card * (((H.neighborFinset q) ∩ S).card-1)) := by
  classical
  let f : V → ℕ := fun q => ((H.neighborFinset q) ∩ S).card * (((H.neighborFinset q) ∩ S).card-1)
  have hAs : ∀ a ∈ A, B.card ≤ ((H.neighborFinset a) ∩ S).card := by
    intro a ha
    apply Finset.card_le_card
    intro b hb
    exact Finset.mem_inter.mpr ⟨by simpa using hcross a ha b hb,hB hb⟩
  have hBs : ∀ b ∈ B, 4 ≤ ((H.neighborFinset b) ∩ S).card := by
    intro b hb
    have hs : A ⊆ (H.neighborFinset b) ∩ S := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨by simpa using (hcross a ha b hb).symm,hA ha⟩
    have hc := Finset.card_le_card hs
    omega
  have hAlow : A.card*(B.card*(B.card-1)) ≤ ∑ a ∈ A, f a := by
    have h := Finset.sum_le_sum (s := A) (f := fun _ => B.card*(B.card-1)) (g := f) (by
      intro a ha
      have hc := hAs a ha
      have hd := Nat.sub_le_sub_right hc 1
      exact Nat.mul_le_mul hc hd)
    simpa [Nat.mul_comm] using h
  have hBlow : B.card*12 ≤ ∑ b ∈ B, f b := by
    have h := Finset.sum_le_sum (s := B) (f := fun _ => 12) (g := f) (by
      intro b hb
      have hc := hBs b hb
      have hd := Nat.sub_le_sub_right hc 1
      have hh := Nat.mul_le_mul hc hd
      simpa using hh)
    simpa [Nat.mul_comm] using h
  have hsub : A ∪ B ⊆ S := Finset.union_subset hA hB
  have hsum : (A ∪ B).sum f ≤ S.sum f := Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_union hdis] at hsum
  dsimp [f] at *
  rw [hAcard] at hAlow
  simp only [Nat.mul_assoc] at hAlow ⊢
  omega
