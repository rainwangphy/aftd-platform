import AFTD.Prelude

/-!
# three_token_k2n_explicit_family

Topic: graphs   Node: fa022f7b4323

Provenance: helper lemma. Explicit construction for three_token_k2n_has_dominating_set and OP-666.

The candidate family of three-token configurations: all configurations with left vertex 0 and a same-half pair on the right, the right-side triple 0,1,2, and configurations with both left vertices and a right vertex numbered at least 3.
-/

noncomputable def three_token_k2n_explicit_family (n : ℕ) (hn : 4 ≤ n) :
    Finset {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3} := by
  classical
  let e : Fin n ↪ Fin 2 ⊕ Fin n := ⟨Sum.inr, Sum.inr_injective⟩
  let b0 : Fin n := ⟨0, by omega⟩
  let b1 : Fin n := ⟨1, by omega⟩
  let b2 : Fin n := ⟨2, by omega⟩
  exact Finset.univ.filter fun z =>
    (∃ B : Finset (Fin n), B.card = 2 ∧
      (B ⊆ Finset.univ.filter (fun b : Fin n => b.val < n / 2) ∨
       B ⊆ Finset.univ.filter (fun b : Fin n => n / 2 ≤ b.val)) ∧
      z.val = insert (Sum.inl 0) (B.map e)) ∨
    z.val = {Sum.inr b0, Sum.inr b1, Sum.inr b2} ∨
    (∃ b : Fin n, 3 ≤ b.val ∧ z.val = {Sum.inl 0, Sum.inl 1, Sum.inr b})
