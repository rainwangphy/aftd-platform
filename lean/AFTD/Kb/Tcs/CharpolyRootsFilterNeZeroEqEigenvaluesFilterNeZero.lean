import AFTD.Prelude
import AFTD.Kb.Tcs.MultisetFilterMapOfRealEq

/-!
# charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero

Topic: quantum   Node: cf5222c045d2

Provenance: formalization of a published result. Source: QuantumInfo, `charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/VonNeumann.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ : Type*} in
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] in
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] in
variable {dA dB dC dA₁ dA₂ : Type*} in
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂] in
variable {𝕜 : Type*} [RCLike 𝕜] in
variable {α : ℝ} in
open scoped InnerProductSpace RealInnerProductSpace in
lemma charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    A.charpoly.roots.filter (· ≠ 0) = ((Finset.univ.val.map hA.eigenvalues).filter (· ≠ 0)).map RCLike.ofReal := by
  convert congr_arg _ ?_;
  rw [ multiset_filter_map_ofReal_eq ];
  -- Since A is Hermitian, its characteristic polynomial is equal to the product of (X - eigenvalue) over all eigenvalues.
  have h_charpoly : A.charpoly = Multiset.prod (Multiset.map (fun i => Polynomial.X - Polynomial.C (RCLike.ofReal (hA.eigenvalues i))) (Finset.univ.val)) := by
    convert! Matrix.IsHermitian.charpoly_eq hA using 1;
  rw [ h_charpoly, Polynomial.roots_multiset_prod ];
  · simp [ Multiset.bind_map ];
  · simp [ Polynomial.X_sub_C_ne_zero ]
