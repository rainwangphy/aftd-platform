import AFTD.Prelude
import AFTD.Kb.Tcs.McdoLe
import AFTD.Kb.Tcs.IsPosetLinearExtension
import AFTD.Kb.Tcs.LinearExtensionCompAutomorphism
import AFTD.Kb.Tcs.ChainStepElementMapAutomorphism
import AFTD.Kb.Tcs.MaximalChainLowerSet
import AFTD.Kb.Tcs.MaximalChainMapAutomorphism
import AFTD.Kb.Tcs.DiamondMove
import AFTD.Kb.Tcs.DiffersInOnePosition
import AFTD.Kb.Tcs.ChainStepElement

/-!
# poset_automorphism_induces_isomorphic_mcdo

Topic: combinatorics   Node: 615cbea6cba9

Provenance: formalization of a published result. Source: arXiv:2611.26888 Theorem 1.2

Let P be a finite partially ordered set with linear extension l : P → Fin (Fintype.card P), and let f : P ≃o P be a poset automorphism. Then the linear extensions l and l ∘ f induce isomorphic maximal chain descent orders mcdo_le l and mcdo_le (l ∘ f) on the maximal chains of order ideals of P, that is, Nonempty (mcdo_le l ≃r mcdo_le (l ∘ f)).
-/

open Relation

private theorem poset_automorphism_induces_isomorphic_mcdo_maxchain_ext {P : Type*} [PartialOrder P] [Fintype P]
    {M N : MaximalChainLowerSet P} (h : M.chain = N.chain) : M = N := by
  cases M; cases N; simp_all

private theorem poset_automorphism_induces_isomorphic_mcdo_mcma_symm_comp {P : Type*} [PartialOrder P] [Fintype P]
    (f : P ≃o P) (M : MaximalChainLowerSet P) :
    maximal_chain_map_automorphism f (maximal_chain_map_automorphism f.symm M) = M := by
  apply poset_automorphism_induces_isomorphic_mcdo_maxchain_ext
  funext j
  show LowerSet.map f.symm ((maximal_chain_map_automorphism f.symm M).chain j) = M.chain j
  show LowerSet.map f.symm (LowerSet.map (f.symm).symm (M.chain j)) = M.chain j
  rw [OrderIso.symm_symm]
  rw [LowerSet.map_map]
  have htr : f.trans f.symm = OrderIso.refl P := by ext x; simp
  rw [htr]
  simp [LowerSet.map_refl]

private theorem poset_automorphism_induces_isomorphic_mcdo_diffs_automorphism {P : Type*} [PartialOrder P] [Fintype P]
    (f : P ≃o P) (M M' : MaximalChainLowerSet P) (j : Fin (Fintype.card P + 1)) :
    differs_in_one_position (maximal_chain_map_automorphism f M)
      (maximal_chain_map_automorphism f M') j ↔ differs_in_one_position M M' j := by
  unfold differs_in_one_position
  simp only [maximal_chain_map_automorphism]
  constructor
  · rintro ⟨hne, heq⟩
    refine ⟨?_, ?_⟩
    · intro h; exact hne (by rw [h])
    · intro k hk; exact (LowerSet.map f.symm).injective (heq k hk)
  · rintro ⟨hne, heq⟩
    refine ⟨?_, ?_⟩
    · intro h; exact hne ((LowerSet.map f.symm).injective h)
    · intro k hk; rw [heq k hk]

private theorem poset_automorphism_induces_isomorphic_mcdo_diamond_move_automorphism {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) (f : P ≃o P) (M M' : MaximalChainLowerSet P) :
    diamond_move (l ∘ f) (maximal_chain_map_automorphism f M)
      (maximal_chain_map_automorphism f M') ↔ diamond_move l M M' := by
  constructor
  · rintro ⟨i, hi, hdiff, x, y, hx, hy, hlt⟩
    have hx' : chain_step_element M i (f x) :=
      (chain_step_element_map_automorphism f M i (f x)).mpr (by simpa using hx)
    have hy' : chain_step_element M ⟨i.1 + 1, hi⟩ (f y) :=
      (chain_step_element_map_automorphism f M ⟨i.1 + 1, hi⟩ (f y)).mpr (by simpa using hy)
    have hdiff' : differs_in_one_position M M' ⟨i.1 + 1, Nat.lt_succ_of_lt hi⟩ :=
      (poset_automorphism_induces_isomorphic_mcdo_diffs_automorphism f M M' ⟨i.1 + 1, Nat.lt_succ_of_lt hi⟩).mp (by simpa using hdiff)
    exact ⟨i, hi, hdiff', f x, f y, hx', hy', by simpa [Function.comp] using hlt⟩
  · rintro ⟨i, hi, hdiff, x, y, hx, hy, hlt⟩
    have hdiff' : differs_in_one_position (maximal_chain_map_automorphism f M)
        (maximal_chain_map_automorphism f M') ⟨i.1 + 1, Nat.lt_succ_of_lt hi⟩ :=
      (poset_automorphism_induces_isomorphic_mcdo_diffs_automorphism f M M' ⟨i.1 + 1, Nat.lt_succ_of_lt hi⟩).mpr (by simpa using hdiff)
    exact ⟨i, hi, hdiff',
      f.symm x, f.symm y,
      (chain_step_element_map_automorphism f M i x).mp hx,
      (chain_step_element_map_automorphism f M ⟨i.1 + 1, hi⟩ y).mp hy,
      by simpa [Function.comp] using hlt⟩

private theorem poset_automorphism_induces_isomorphic_mcdo_mcma_symm_cancel {P : Type*} [PartialOrder P] [Fintype P]
    (f : P ≃o P) (M : MaximalChainLowerSet P) :
    maximal_chain_map_automorphism f.symm (maximal_chain_map_automorphism f M) = M := by
  simpa using poset_automorphism_induces_isomorphic_mcdo_mcma_symm_comp (f := f.symm) M

/-- Poset automorphisms induce isomorphic maximal chain descent orders (Theorem 1.2). -/
theorem poset_automorphism_induces_isomorphic_mcdo
    {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) (hl : is_poset_linear_extension l) (f : P ≃o P) :
    Nonempty (mcdo_le l ≃r mcdo_le (l ∘ f)) := by
  let eqv : MaximalChainLowerSet P ≃ MaximalChainLowerSet P :=
    { toFun := maximal_chain_map_automorphism f
      invFun := maximal_chain_map_automorphism f.symm
      left_inv := fun M => poset_automorphism_induces_isomorphic_mcdo_mcma_symm_cancel f M
      right_inv := fun M => poset_automorphism_induces_isomorphic_mcdo_mcma_symm_comp f M }
  refine ⟨{ toEquiv := eqv, map_rel_iff' := ?_ }⟩
  intro a b
  change mcdo_le (l ∘ f) (maximal_chain_map_automorphism f a) (maximal_chain_map_automorphism f b) ↔
    mcdo_le l a b
  unfold mcdo_le
  constructor
  · intro h
    have hbwd : diamond_move (l ∘ f) ≤
        Function.onFun (diamond_move l) (maximal_chain_map_automorphism f.symm) := by
      intro x y hxy
      have h' : diamond_move (l ∘ f) (maximal_chain_map_automorphism f (maximal_chain_map_automorphism f.symm x))
          (maximal_chain_map_automorphism f (maximal_chain_map_automorphism f.symm y)) := by
        rw [poset_automorphism_induces_isomorphic_mcdo_mcma_symm_comp f x,
            poset_automorphism_induces_isomorphic_mcdo_mcma_symm_comp f y]
        exact hxy
      exact (poset_automorphism_induces_isomorphic_mcdo_diamond_move_automorphism l f
        (maximal_chain_map_automorphism f.symm x)
        (maximal_chain_map_automorphism f.symm y)).mp h'
    have h' := Relation.ReflTransGen.lift (maximal_chain_map_automorphism f.symm) hbwd
      (maximal_chain_map_automorphism f a) (maximal_chain_map_automorphism f b) h
    simp only [Function.onFun] at h'
    rw [poset_automorphism_induces_isomorphic_mcdo_mcma_symm_cancel f a,
        poset_automorphism_induces_isomorphic_mcdo_mcma_symm_cancel f b] at h'
    exact h'
  · intro h
    have hfwd : diamond_move l ≤
        Function.onFun (diamond_move (l ∘ f)) (maximal_chain_map_automorphism f) := by
      intro x y hxy
      exact (poset_automorphism_induces_isomorphic_mcdo_diamond_move_automorphism l f x y).mpr hxy
    exact Relation.ReflTransGen.lift (maximal_chain_map_automorphism f) hfwd a b h
