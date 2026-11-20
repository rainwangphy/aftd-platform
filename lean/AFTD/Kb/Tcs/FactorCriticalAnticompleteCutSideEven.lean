import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factor_critical_anticomplete_cut_side_even

Topic: graphs   Node: ab893009db21

Provenance: helper lemma. Parity of crossing cut sides in the OP-1957 strict-interior route.

In a finite k-factor-critical graph, if two disjoint anticomplete vertex sets have a complement of exactly k vertices, then the first set has even cardinality.
-/

theorem in1076_factorcritical_odd_union_no_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (hodd : Odd A.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    ¬ ∃ P : (G.induce {v | v ∈ A ∨ v ∈ B}).Subgraph, P.IsPerfectMatching := by
  classical
  rintro ⟨P, hP⟩
  let C : Set {v : V // v ∈ A ∨ v ∈ B} := {v | v.val ∈ A}
  let R := P.induce C
  have hRmatch : R.IsMatching := by
    intro a ha
    have haA : a.val ∈ A := ha
    obtain ⟨b, hab, huniq⟩ := hP.1 (hP.2 a)
    have hbA : b.val ∈ A := by
      rcases b.property with hbA | hbB
      · exact hbA
      · exact False.elim (hcross a.val haA b.val hbB (P.adj_sub hab))
    refine ⟨b, ⟨haA, hbA, hab⟩, ?_⟩
    intro c hc
    exact huniq c hc.2.2
  let e : R.verts ≃ {v : V // v ∈ A} := {
    toFun := fun ⟨⟨v, hv⟩, ha⟩ => ⟨v, ha⟩
    invFun := fun ⟨v, hv⟩ => ⟨⟨v, Or.inl hv⟩, hv⟩
    left_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro v; apply Subtype.ext; rfl }
  have hcard : R.verts.toFinset.card = A.card := by
    rw [Set.toFinset_card]
    have he := Fintype.card_congr e
    simpa using he
  have heven := hRmatch.even_card
  rw [hcard] at heven
  exact (Nat.not_odd_iff_even.mpr heven) hodd

theorem factor_critical_anticomplete_cut_side_even
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (hG : is_k_factor_critical G k) (A B : Finset V)
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hcut : ((Finset.univ : Finset V) \ (A ∪ B)).card = k) : Even A.card := by
  classical
  by_contra hn
  have hodd : Odd A.card := Nat.not_even_iff_odd.mp hn
  let C : Finset V := Finset.univ \ (A ∪ B)
  have hm := hG C hcut
  have heq : (C : Set V)ᶜ = {v | v ∈ A ∨ v ∈ B} := by
    ext v
    simp [C] <;> tauto
  have hm' : ∃ P : (G.induce {v | v ∈ A ∨ v ∈ B}).Subgraph, P.IsPerfectMatching := by
    rw [← heq]
    exact hm
  exact in1076_factorcritical_odd_union_no_matching G A B hAB hodd hcross hm'
