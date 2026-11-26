import AFTD.Prelude

/-!
# op874_saturated_same_bit_cover_forces_exact

Topic: graphs   Node: c517a131ac97

Provenance: helper lemma. Low-port counting reduction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

If the same-bit edge set of a finite simple graph has as many edges as vertices and every vertex selects one incident edge while every same-bit edge is selected at an endpoint, every vertex selects a same-bit edge and every same-bit edge is selected at exactly one endpoint.
-/

theorem op874_saturated_same_bit_cover_forces_exact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → Bool) (S : Finset (Sym2 V)) (p : V → V)
    (hsub : S ⊆ G.edgeFinset)
    (hreq : ∀ u v, G.Adj u v → (s(u,v) ∈ S ↔ b u = b v))
    (hcard : S.card = Fintype.card V)
    (hadj : ∀ v, G.Adj v (p v))
    (hcover : ∀ u v, G.Adj u v → b u = b v → p u = v ∨ p v = u) :
    (∀ v, b v = b (p v)) ∧
    (∀ u v, G.Adj u v → b u = b v → (p u = v ↔ p v ≠ u)) := by
  classical
  let f : V → Sym2 V := fun v => s(v, p v)
  have hS_sub : S ⊆ Finset.univ.image f := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have he_edge : s(u, v) ∈ G.edgeFinset := hsub he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he_edge
      have hbuv : b u = b v := (hreq u v he_edge).mp he
      rcases hcover u v he_edge hbuv with hpu | hpv
      · rw [Finset.mem_image]
        exact ⟨u, Finset.mem_univ u, by dsimp [f]; rw [hpu]⟩
      · rw [Finset.mem_image]
        exact ⟨v, Finset.mem_univ v, by dsimp [f]; rw [hpv, Sym2.eq_swap]⟩
  have hcard_le : (Finset.univ.image f).card ≤ S.card := by
    rw [hcard]
    calc (Finset.univ.image f).card ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ
  have hS_eq : S = Finset.univ.image f := Finset.eq_of_subset_of_card_le hS_sub hcard_le
  have hf_inj : Function.Injective f := by
    have h_inj : Set.InjOn f (Finset.univ : Finset V) := by
      apply Finset.injOn_of_card_image_eq
      rw [Finset.card_univ, ← hcard, ← hS_eq]
    intro x y hxy
    exact h_inj (Finset.mem_univ x) (Finset.mem_univ y) hxy
  have h1 : ∀ v, b v = b (p v) := by
    intro v
    have hfv : f v ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    rw [← hS_eq] at hfv
    exact (hreq v (p v) (hadj v)).mp hfv
  have h2 : ∀ u v, G.Adj u v → b u = b v → (p u = v ↔ p v ≠ u) := by
    intro u v hadj_uv hbuv
    have hcov := hcover u v hadj_uv hbuv
    have hnot_both : ¬ (p u = v ∧ p v = u) := by
      rintro ⟨hpu, hpv⟩
      have hfeq : f u = f v := by
        dsimp [f]
        rw [hpu, hpv, Sym2.eq_swap]
      have heq := hf_inj hfeq
      exact hadj_uv.ne heq
    constructor
    · intro hpu hpv
      exact hnot_both ⟨hpu, hpv⟩
    · intro hpv_ne
      cases hcov with
      | inl hpu => exact hpu
      | inr hpv => exact False.elim (hpv_ne hpv)
  exact ⟨h1, h2⟩
