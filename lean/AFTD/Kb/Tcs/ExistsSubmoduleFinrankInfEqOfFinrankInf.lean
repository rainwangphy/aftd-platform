import AFTD.Prelude

/-!
# exists_submodule_finrank_inf_eq_of_finrank_inf

Topic: combinatorics   Node: 5ec81c6d7d4a

Provenance: formalization of a published result. Source: arXiv:2610.17631 (Complete mappings stabilizing Sylow 2-subgroups in central extensions), Lemma 4.1 (stated here for a finite-dimensional ambient space).

Let E, F be k-dimensional subspaces of a finite-dimensional vector space with dim(E ∩ F) = k − j, 0 ≤ j ≤ k. Then some k-dimensional subspace W has dim(E ∩ W) = dim(W ∩ F) = k − j.
-/

open Submodule

lemma exists_submodule_finrank_inf_eq_of_finrank_inf_relative_complement
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {C E : Submodule K V} (hCE : C ≤ E) :
    ∃ E₁ : Submodule K V, E₁ ≤ E ∧ C ⊔ E₁ = E ∧ C ⊓ E₁ = ⊥ := by
  obtain ⟨E₁', hcomp⟩ := Submodule.exists_isCompl (C.comap E.subtype)
  refine ⟨E₁'.map E.subtype, ?_, ?_, ?_⟩
  · exact Submodule.map_subtype_le E E₁'
  · have hC : C = map E.subtype (comap E.subtype C) := by
      rw [map_comap_subtype, inf_comm, inf_of_le_left hCE]
    rw [hC, ← Submodule.map_sup, hcomp.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  · have hC : C = map E.subtype (comap E.subtype C) := by
      rw [map_comap_subtype, inf_comm, inf_of_le_left hCE]
    rw [hC, ← Submodule.map_inf E.subtype (Submodule.subtype_injective E), hcomp.inf_eq_bot, Submodule.map_bot]

def exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E₁ F₁ : Submodule K V) (f : ↥E₁ ≃ₗ[K] ↥F₁) : ↥E₁ →ₗ[K] V :=
  E₁.subtype + F₁.subtype.comp f.toLinearMap

lemma exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_apply
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E₁ F₁ : Submodule K V) (f : ↥E₁ ≃ₗ[K] ↥F₁) (x : E₁) :
    exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap E₁ F₁ f x = (x : V) + (f x : V) := by
  simp [exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap]

lemma exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_injective
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {E F E₁ F₁ : Submodule K V} (hE₁ : E₁ ≤ E) (hF₁ : F₁ ≤ F)
    (hC_E₁ : (E ⊓ F) ⊓ E₁ = ⊥) (f : ↥E₁ ≃ₗ[K] ↥F₁) :
    Function.Injective (exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap E₁ F₁ f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_apply] at hx
  have hx_eq : (x : V) = - (f x : V) := eq_neg_of_add_eq_zero_left hx
  have h1 : (x : V) ∈ E := hE₁ x.2
  have h2 : (x : V) ∈ F := by
    rw [hx_eq]
    exact Submodule.neg_mem F (hF₁ (f x).2)
  have h3 : (x : V) ∈ (E ⊓ F) ⊓ E₁ := Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨h1, h2⟩, x.2⟩
  rw [hC_E₁] at h3
  exact Subtype.ext (Submodule.mem_bot (R := K).mp h3)

lemma exists_submodule_finrank_inf_eq_of_finrank_inf_range_graphMap_inf_E_eq_bot
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {E F E₁ F₁ : Submodule K V}
    (hE₁ : E₁ ≤ E) (hF₁ : F₁ ≤ F) (hC_F₁ : (E ⊓ F) ⊓ F₁ = ⊥)
    (f : ↥E₁ ≃ₗ[K] ↥F₁) :
    (exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap E₁ F₁ f).range ⊓ E = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  rcases hv with ⟨hvG, hvE⟩
  rw [LinearMap.mem_range] at hvG
  rcases hvG with ⟨x, rfl⟩
  have hfx : (f x : V) = (exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap E₁ F₁ f x) - (x : V) := by
    rw [exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_apply, add_sub_cancel_left]
  have hfx_in_E : (f x : V) ∈ E := by
    rw [hfx]
    exact Submodule.sub_mem E hvE (hE₁ x.2)
  have hfx_in_F : (f x : V) ∈ F := hF₁ (f x).2
  have hfx_in_C_F₁ : (f x : V) ∈ (E ⊓ F) ⊓ F₁ :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hfx_in_E, hfx_in_F⟩, (f x).2⟩
  rw [hC_F₁, Submodule.mem_bot (R := K)] at hfx_in_C_F₁
  have hfx0 : f x = 0 := Subtype.ext hfx_in_C_F₁
  have hx0 : x = 0 := map_eq_zero_iff f.toLinearMap (LinearEquiv.injective f) |>.mp hfx0
  simp [hx0, exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_apply]

lemma exists_submodule_finrank_inf_eq_of_finrank_inf_range_graphMap_inf_F_eq_bot
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {E F E₁ F₁ : Submodule K V}
    (hE₁ : E₁ ≤ E) (hF₁ : F₁ ≤ F) (hC_E₁ : (E ⊓ F) ⊓ E₁ = ⊥)
    (f : ↥E₁ ≃ₗ[K] ↥F₁) :
    (exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap E₁ F₁ f).range ⊓ F = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  rcases hv with ⟨hvG, hvF⟩
  rw [LinearMap.mem_range] at hvG
  rcases hvG with ⟨x, rfl⟩
  have hx_sub : (x : V) = (exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap E₁ F₁ f x) - (f x : V) := by
    rw [exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_apply, add_sub_cancel_right]
  have hx_in_F : (x : V) ∈ F := by
    rw [hx_sub]
    exact Submodule.sub_mem F hvF (hF₁ (f x).2)
  have hx_in_E : (x : V) ∈ E := hE₁ x.2
  have hx_in_C_E₁ : (x : V) ∈ (E ⊓ F) ⊓ E₁ :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hx_in_E, hx_in_F⟩, x.2⟩
  rw [hC_E₁, Submodule.mem_bot (R := K)] at hx_in_C_E₁
  have hx0 : x = 0 := Subtype.ext hx_in_C_E₁
  simp [hx0, exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_apply]

theorem exists_submodule_finrank_inf_eq_of_finrank_inf {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (k j : ℕ) (hjk : j ≤ k) (E F : Submodule K V)
    (hE : Module.finrank K E = k) (hF : Module.finrank K F = k)
    (hEF : Module.finrank K ↥(E ⊓ F) = k - j) :
    ∃ W : Submodule K V, Module.finrank K W = k ∧ Module.finrank K ↥(E ⊓ W) = k - j ∧
      Module.finrank K ↥(W ⊓ F) = k - j := by
  set C := E ⊓ F
  have hCE : C ≤ E := inf_le_left
  have hCF : C ≤ F := inf_le_right
  obtain ⟨E₁, hE₁le, hCE_sup, hCE_inf⟩ :=
    exists_submodule_finrank_inf_eq_of_finrank_inf_relative_complement hCE
  obtain ⟨F₁, hF₁le, hCF_sup, hCF_inf⟩ :=
    exists_submodule_finrank_inf_eq_of_finrank_inf_relative_complement hCF
  have h_dim_E₁ : Module.finrank K ↥E₁ = j := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq C E₁
    rw [hCE_sup, hCE_inf, finrank_bot, hE, hEF] at h
    omega
  have h_dim_F₁ : Module.finrank K ↥F₁ = j := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq C F₁
    rw [hCF_sup, hCF_inf, finrank_bot, hF, hEF] at h
    omega
  have h_dim_eq : Module.finrank K ↥E₁ = Module.finrank K ↥F₁ := by
    rw [h_dim_E₁, h_dim_F₁]
  let f : ↥E₁ ≃ₗ[K] ↥F₁ := LinearEquiv.ofFinrankEq (↥E₁) (↥F₁) h_dim_eq
  let g := exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap E₁ F₁ f
  let Γ := g.range
  have hginj : Function.Injective g :=
    exists_submodule_finrank_inf_eq_of_finrank_inf_graphMap_injective hE₁le hF₁le hCE_inf f
  have h_dim_Γ : Module.finrank K ↥Γ = j := by
    rw [LinearMap.finrank_range_of_inj hginj, h_dim_E₁]
  have hΓE : Γ ⊓ E = ⊥ :=
    exists_submodule_finrank_inf_eq_of_finrank_inf_range_graphMap_inf_E_eq_bot hE₁le hF₁le hCF_inf f
  have hΓF : Γ ⊓ F = ⊥ :=
    exists_submodule_finrank_inf_eq_of_finrank_inf_range_graphMap_inf_F_eq_bot hE₁le hF₁le hCE_inf f
  let W := C ⊔ Γ
  refine ⟨W, ?_, ?_, ?_⟩
  · dsimp [W]
    have hCΓ_le : C ⊓ Γ ≤ E ⊓ Γ := inf_le_inf_right Γ hCE
    have hEΓ : E ⊓ Γ = ⊥ := by rw [inf_comm, hΓE]
    have hCΓ : C ⊓ Γ = ⊥ := le_bot_iff.mp (hCΓ_le.trans (le_of_eq hEΓ))
    have h := Submodule.finrank_sup_add_finrank_inf_eq C Γ
    rw [hCΓ, finrank_bot, hEF, h_dim_Γ] at h
    omega
  · have hEW : E ⊓ W = C := by
      rw [inf_comm]
      change (C ⊔ Γ) ⊓ E = C
      rw [sup_inf_assoc_of_le _ hCE, hΓE, sup_bot_eq]
    rw [hEW, hEF]
  · have hWF : W ⊓ F = C := by
      change (C ⊔ Γ) ⊓ F = C
      rw [sup_inf_assoc_of_le _ hCF, hΓF, sup_bot_eq]
    rw [hWF, hEF]
