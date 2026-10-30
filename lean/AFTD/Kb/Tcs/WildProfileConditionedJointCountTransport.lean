import AFTD.Prelude

/-!
# wild_profile_conditioned_joint_count_transport

Topic: graphs   Node: 2f5b01e9eeae

Provenance: helper lemma. IN-364 / OP-306, continuation of the finite weighted-partition route for https://arxiv.org/html/2610.22142v1, Sections3.3 and6. Standard permutation-orbit background: Matchings and Representation Theory (2018), Section4.10, https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content. The witness triple system is standard incidence data; these are route helpers or finite method diagnostics. No wild-number bound, new exact sharpness case, general sign theorem, or research advance is claimed.

For a finite vertex type, finite block type, arbitrary block profile p, chosen block b and vertex subset S, and any finite set of color relations R_c,T_c simultaneously transported by a vertex permutation e, the number of permutations making every selected color have an empty nontrivial block cut and making block b equal S is unchanged after replacing the relations by T_c and S by its image under e. A simultaneous isomorphism is a hypothesis; no classification by cycle data is asserted.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

noncomputable def wild_profile_bad {V B : Type*} [Fintype B]
    (p : V → B) (R : V → V → Prop) : Prop :=
  ∃ S : Finset B, S.Nonempty ∧ S ≠ univ ∧
    ∀ u v, p u ∈ S → p v ∉ S → ¬ R u v

def wild_profile_permute {V B : Type*} (p : V → B) (σ : Equiv.Perm V) : V → B :=
  fun v => p (σ.symm v)

noncomputable def wild_profile_fiber {V B : Type*} [Fintype V]
    (p : V → B) (b : B) : Finset V := univ.filter fun v => p v = b

theorem wild_profile_bad_relabel {V B : Type*} [Fintype B]
    (p : V → B) (R T : V → V → Prop) (e : Equiv.Perm V)
    (h : ∀ u v, T (e u) (e v) ↔ R u v) :
    wild_profile_bad (wild_profile_permute p e) T ↔ wild_profile_bad p R := by
  classical
  constructor
  · rintro ⟨S,hS,hS',hcut⟩
    refine ⟨S,hS,hS',?_⟩
    intro u v hu hv huv
    apply hcut (e u) (e v)
    · simpa [wild_profile_permute] using hu
    · simpa [wild_profile_permute] using hv
    · exact (h u v).mpr huv
  · rintro ⟨S,hS,hS',hcut⟩
    refine ⟨S,hS,hS',?_⟩
    intro u v hu hv huv
    apply hcut (e.symm u) (e.symm v) hu hv
    apply (h (e.symm u) (e.symm v)).mp
    simpa using huv

theorem wild_profile_permute_trans {V B : Type*}
    (p : V → B) (σ e : Equiv.Perm V) :
    wild_profile_permute p (σ.trans e) =
      wild_profile_permute (wild_profile_permute p σ) e := by
  rfl

theorem wild_profile_fiber_relabel {V B : Type*} [Fintype V]
    (p : V → B) (b : B) (e : Equiv.Perm V) :
    wild_profile_fiber (wild_profile_permute p e) b = (wild_profile_fiber p b).image e := by
  classical
  unfold wild_profile_fiber wild_profile_permute
  ext v
  simp only [mem_filter,mem_univ,true_and,mem_image]
  constructor
  · intro h
    exact ⟨e.symm v,h,e.apply_symm_apply v⟩
  · rintro ⟨u,hu,rfl⟩
    simpa using hu

noncomputable def wild_profile_joint_bad_count {V B C : Type*}
    [Fintype V] [Fintype B]
    (p : V → B) (R : C → V → V → Prop) (colors : Finset C) : ℕ :=
  (univ.filter fun σ : Equiv.Perm V =>
    ∀ c ∈ colors, wild_profile_bad (wild_profile_permute p σ) (R c)).card

theorem wild_profile_joint_bad_count_transport {V B C : Type*}
    [Fintype V] [Fintype B]
    (p : V → B) (R T : C → V → V → Prop) (colors : Finset C)
    (e : Equiv.Perm V) (h : ∀ c ∈ colors, ∀ u v, T c (e u) (e v) ↔ R c u v) :
    wild_profile_joint_bad_count p R colors = wild_profile_joint_bad_count p T colors := by
  classical
  unfold wild_profile_joint_bad_count
  apply Finset.card_bij (fun σ _ => σ.trans e)
  · intro σ hσ
    simp only [mem_filter,mem_univ,true_and] at hσ ⊢
    intro c hc
    rw [wild_profile_permute_trans]
    exact (wild_profile_bad_relabel (wild_profile_permute p σ) (R c) (T c) e (h c hc)).mpr
      (hσ c hc)
  · intro σ _ τ _ he
    ext v
    exact e.injective (congrArg (fun f : Equiv.Perm V => f v) he)
  · intro τ hτ
    refine ⟨τ.trans e.symm,?_,?_⟩
    · simp only [mem_filter,mem_univ,true_and] at hτ ⊢
      intro c hc
      rw [wild_profile_permute_trans]
      apply (wild_profile_bad_relabel (wild_profile_permute p τ) (T c) (R c) e.symm ?_).mpr
        (hτ c hc)
      intro u v
      simpa using (h c hc (e.symm u) (e.symm v)).symm
    · ext v
      simp

noncomputable def wild_profile_conditioned_joint_bad_count {V B C : Type*}
    [Fintype V] [Fintype B]
    (p : V → B) (b : B) (S : Finset V)
    (R : C → V → V → Prop) (colors : Finset C) : ℕ :=
  (univ.filter fun σ : Equiv.Perm V =>
    wild_profile_fiber (wild_profile_permute p σ) b = S ∧
    ∀ c ∈ colors, wild_profile_bad (wild_profile_permute p σ) (R c)).card

theorem wild_profile_conditioned_joint_count_transport {V B C : Type*}
    [Fintype V] [Fintype B]
    (p : V → B) (b : B) (S : Finset V)
    (R T : C → V → V → Prop) (colors : Finset C)
    (e : Equiv.Perm V) (h : ∀ c ∈ colors, ∀ u v, T c (e u) (e v) ↔ R c u v) :
    wild_profile_conditioned_joint_bad_count p b S R colors =
      wild_profile_conditioned_joint_bad_count p b (S.image e) T colors := by
  classical
  unfold wild_profile_conditioned_joint_bad_count
  apply Finset.card_bij (fun σ _ => σ.trans e)
  · intro σ hσ
    simp only [mem_filter,mem_univ,true_and] at hσ ⊢
    constructor
    · rw [wild_profile_permute_trans,wild_profile_fiber_relabel,hσ.1]
    · intro c hc
      rw [wild_profile_permute_trans]
      exact (wild_profile_bad_relabel (wild_profile_permute p σ) (R c) (T c) e (h c hc)).mpr
        (hσ.2 c hc)
  · intro σ _ τ _ he
    ext v
    exact e.injective (congrArg (fun f : Equiv.Perm V => f v) he)
  · intro τ hτ
    refine ⟨τ.trans e.symm,?_,?_⟩
    · simp only [mem_filter,mem_univ,true_and] at hτ ⊢
      constructor
      · rw [wild_profile_permute_trans,wild_profile_fiber_relabel,hτ.1]
        simp only [Finset.image_image]
        simp
      · intro c hc
        rw [wild_profile_permute_trans]
        apply (wild_profile_bad_relabel (wild_profile_permute p τ) (T c) (R c) e.symm ?_).mpr
          (hτ.2 c hc)
        intro u v
        simpa using (h c hc (e.symm u) (e.symm v)).symm
    · ext v
      simp
