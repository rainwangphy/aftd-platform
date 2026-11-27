import AFTD.Prelude

/-!
# op874_permutation_disjoint_cover

Topic: graphs   Node: e3e2e0735869

Provenance: helper lemma. Cycle-interface counting for OP-874, based on the local-state criterion in arXiv:2610.41950.

Let A and B be disjoint subsets of a finite set and let σ be a permutation. If every element v is in A or its image σ(v) is in B, then A and B cover the entire set.
-/

theorem op874_permutation_disjoint_cover
    {V : Type*} [Fintype V] [DecidableEq V] (σ : V ≃ V) (A B : Finset V)
    (hdis : Disjoint A B) (hcover : ∀ v, v ∈ A ∨ σ v ∈ B) :
    ∀ v, v ∈ A ∨ v ∈ B := by
  let B' : Finset V := B.map σ.symm.toEmbedding
  have hmem (v : V) : v ∈ B' ↔ σ v ∈ B := by
    simp [B']
  have hunion : A ∪ B' = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact (hcover v).imp_right (fun h => (hmem v).2 h)
  have hge : Fintype.card V ≤ A.card + B.card := by
    calc
      Fintype.card V = (A ∪ B').card := by rw [hunion, Finset.card_univ]
      _ ≤ A.card + B'.card := Finset.card_union_le _ _
      _ = A.card + B.card := by simp [B']
  have hle : (A ∪ B).card ≤ Fintype.card V := Finset.card_le_univ _
  have heq : (A ∪ B).card = Fintype.card V := by
    rw [Finset.card_union_of_disjoint hdis]
    rw [Finset.card_union_of_disjoint hdis] at hle
    omega
  have hall : A ∪ B = Finset.univ := Finset.eq_univ_of_card _ heq
  intro v
  have hv : v ∈ A ∪ B := by rw [hall]; exact Finset.mem_univ _
  simpa only [Finset.mem_union] using hv
