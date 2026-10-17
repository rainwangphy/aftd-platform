import AFTD.Prelude

/-!
# Multiset.map_univ_eq_iff

Topic: quantum   Node: a39c014a25c7

Provenance: formalization of a published result. Source: QuantumInfo, `Multiset.map_univ_eq_iff`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Misc.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If two functions from finite types have the same multiset of values, there exists a bijection between the domains that commutes with the functions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- If two functions from finite types have the same multiset of values, there exists a bijection between the domains that commutes with the functions. -/
lemma Multiset.map_univ_eq_iff {α β : Type*} [Fintype α] (f g : α → β) :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val ↔ ∃ (e : α ≃ α), f = g ∘ e := by
  apply Iff.intro
  · intro a
    classical
    -- Since these two multisets are equal, their elements must be equal up to permutation.
    have h_perm : ∃ e : α ≃ α, ∀ x, f x = g (e x) := by
      have h_count_eq : ∀ y : β, Finset.card (Finset.filter (fun x => f x = y) Finset.univ) = Finset.card (Finset.filter (fun x => g x = y) Finset.univ) := by
        intro y;
        replace a := congr_arg ( fun m => m.count y ) a;
        simp_all ( config := { decide := Bool.true } ) [ Multiset.count_map ];
        simp_all [ eq_comm ]
        exact a
      have h_perm : ∀ y : β, ∃ e : { x : α // f x = y } ≃ { x : α // g x = y }, True := by
        intro y
        simp_all only [exists_const_iff, and_true]
        exact ⟨ Fintype.equivOfCardEq <| by simpa [ Fintype.card_subtype ] using h_count_eq y ⟩;
      choose e he using h_perm;
      refine' ⟨ _, _ ⟩;
      exact ( Equiv.sigmaFiberEquiv f ).symm.trans ( Equiv.sigmaCongrRight e ) |> Equiv.trans <| Equiv.sigmaFiberEquiv g;
      intro x
      specialize e ( f x )
      rename_i e_1
      simp_all only [implies_true, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
        Equiv.sigmaFiberEquiv_apply]
      exact Eq.symm ( e_1 ( f x ) ⟨ x, rfl ⟩ |>.2 );
    exact ⟨ h_perm.choose, funext h_perm.choose_spec ⟩;
  · intro a
    obtain ⟨w, h⟩ := a
    subst h
    simp_all only [Function.comp_apply, Finset.univ]
    -- Since $w$ is a bijection, the multiset of $w(x)$ for $x$ in the original multiset is just a permutation of the original multiset.
    have h_perm : Multiset.map (fun x => w x) (Finset.val Fintype.elems) = Finset.val Fintype.elems := by
      exact Multiset.map_univ_val_equiv w;
    conv_rhs => rw [ ← h_perm ];
    simp +zetaDelta at *
