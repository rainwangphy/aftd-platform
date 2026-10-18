import AFTD.Prelude
import AFTD.Kb.Tcs.ListColorableTwoOfTwoInvolutions
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# galvin_bipartite_multigraph_list_edge_colouring_two

Topic: combinatorics   Node: 296d3b107345

Provenance: helper lemma. step towards matroid_sbo_common_list_chromatic_eq

The k = 2 case of Galvin's list edge colouring theorem in fibre form: if every fibre of f and every fibre of g has at most two elements (the bipartite multigraph has maximum degree at most 2, so it is a disjoint union of paths and even cycles), then lists of size at least two admit a proper list edge colouring, i.e. a choice c e ∈ L e with each colour class meeting every fibre of f and of g at most once.
-/

open scoped Classical

noncomputable def galvin_bipartite_multigraph_list_edge_colouring_two_involution {α : Type*} (f : α → ℕ) (e : α) : α :=
  if h : ∃ e' : α, e' ≠ e ∧ f e' = f e then Classical.choose h else e

lemma galvin_bipartite_multigraph_list_edge_colouring_two_unique_other {α : Type*} [Finite α] (f : α → ℕ)
    (hf : ∀ γ : ℕ, {e | f e = γ}.ncard ≤ 2) (e x y : α)
    (hxe : x ≠ e) (hye : y ≠ e) (hfx : f x = f e) (hfy : f y = f e) :
    x = y := by
  by_contra hxy
  have h_sub : ({e, x, y} : Set α) ⊆ {z | f z = f e} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · simp
    · simp [hfx]
    · simp [hfy]
  have h_card := Set.ncard_le_ncard h_sub (Set.toFinite _)
  have hbc_fin : ({x, y} : Set α).Finite := Set.toFinite _
  have ha : e ∉ ({x, y} : Set α) := by simp [hxe.symm, hye.symm]
  have h_eq : ({e, x, y} : Set α) = insert e ({x, y} : Set α) := rfl
  rw [h_eq, Set.ncard_insert_of_notMem ha hbc_fin, Set.ncard_pair hxy] at h_card
  have hf_le := hf (f e)
  linarith

lemma galvin_bipartite_multigraph_list_edge_colouring_two_involution_eq_of_ne {α : Type*} [Finite α] (f : α → ℕ)
    (hf : ∀ γ : ℕ, {e | f e = γ}.ncard ≤ 2) {e₁ e₂ : α} (hne : e₁ ≠ e₂) (hf_eq : f e₁ = f e₂) :
    galvin_bipartite_multigraph_list_edge_colouring_two_involution f e₁ = e₂ := by
  have h : ∃ e', e' ≠ e₁ ∧ f e' = f e₁ := ⟨e₂, Ne.symm hne, hf_eq.symm⟩
  change (if h : ∃ e', e' ≠ e₁ ∧ f e' = f e₁ then Classical.choose h else e₁) = e₂
  rw [dif_pos h]
  have h_spec := Classical.choose_spec h
  exact galvin_bipartite_multigraph_list_edge_colouring_two_unique_other f hf e₁ (Classical.choose h) e₂ h_spec.1 (Ne.symm hne) h_spec.2 hf_eq.symm

lemma galvin_bipartite_multigraph_list_edge_colouring_two_involution_involutive {α : Type*} [Finite α] (f : α → ℕ)
    (hf : ∀ γ : ℕ, {e | f e = γ}.ncard ≤ 2) :
    Function.Involutive (galvin_bipartite_multigraph_list_edge_colouring_two_involution f) := by
  intro e
  change galvin_bipartite_multigraph_list_edge_colouring_two_involution f (if h : ∃ e', e' ≠ e ∧ f e' = f e then Classical.choose h else e) = e
  split_ifs with h
  · have h_spec := Classical.choose_spec h
    exact galvin_bipartite_multigraph_list_edge_colouring_two_involution_eq_of_ne f hf h_spec.1 h_spec.2
  · change (if h' : ∃ e', e' ≠ e ∧ f e' = f e then Classical.choose h' else e) = e
    rw [dif_neg h]

/-- The maximum-degree-two case of Galvin's theorem, in fibre form. -/
theorem galvin_bipartite_multigraph_list_edge_colouring_two {α : Type*} [Finite α] (f g : α → ℕ)
    (hf : ∀ γ : ℕ, {e | f e = γ}.ncard ≤ 2) (hg : ∀ γ : ℕ, {e | g e = γ}.ncard ≤ 2)
    (L : α → Finset ℕ) (hL : ∀ e : α, 2 ≤ (L e).card) :
    ∃ c : α → ℕ, (∀ e : α, c e ∈ L e) ∧
      ∀ γ : ℕ, (∀ e₁ e₂ : α, c e₁ = γ → c e₂ = γ → f e₁ = f e₂ → e₁ = e₂) ∧
        ∀ e₁ e₂ : α, c e₁ = γ → c e₂ = γ → g e₁ = g e₂ → e₁ = e₂ := by
  set p := galvin_bipartite_multigraph_list_edge_colouring_two_involution f
  set q := galvin_bipartite_multigraph_list_edge_colouring_two_involution g
  have hp : Function.Involutive p := galvin_bipartite_multigraph_list_edge_colouring_two_involution_involutive f hf
  have hq : Function.Involutive q := galvin_bipartite_multigraph_list_edge_colouring_two_involution_involutive g hg
  obtain ⟨c, hcL, hc_ne⟩ := list_colorable_two_of_two_involutions (Set.univ : Set α)
    (Set.toFinite _) p q hp hq L (fun e _ => hL e)
  refine ⟨c, fun e => hcL e trivial, fun γ => ⟨?_, ?_⟩⟩
  · intro e₁ e₂ hc1 hc2 hf_eq
    by_contra hne
    have hp_eq : p e₁ = e₂ := galvin_bipartite_multigraph_list_edge_colouring_two_involution_eq_of_ne f hf hne hf_eq
    have hp_ne : p e₁ ≠ e₁ := by rw [hp_eq]; exact Ne.symm hne
    have hc_diff := (hc_ne e₁ trivial).1 trivial hp_ne
    rw [hp_eq, hc1, hc2] at hc_diff
    exact hc_diff rfl
  · intro e₁ e₂ hc1 hc2 hg_eq
    by_contra hne
    have hq_eq : q e₁ = e₂ := galvin_bipartite_multigraph_list_edge_colouring_two_involution_eq_of_ne g hg hne hg_eq
    have hq_ne : q e₁ ≠ e₁ := by rw [hq_eq]; exact Ne.symm hne
    have hc_diff := (hc_ne e₁ trivial).2 trivial hq_ne
    rw [hq_eq, hc1, hc2] at hc_diff
    exact hc_diff rfl
