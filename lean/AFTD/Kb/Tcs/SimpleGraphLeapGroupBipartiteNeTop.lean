import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_leap_group_bipartite_ne_top

Topic: graphs   Node: 439a0ce6a7a5

Provenance: formalization of a published result. Source: scout/2610-18463-the-group-generated-by-a-graph-s-derangements.md:259

Let G be a bipartite simple graph on a finite vertex set with at least 4 vertices. Then its leap group Λ₁(G) is not the full symmetric group on its vertices.
-/

lemma simple_graph_leap_group_bipartite_ne_top_fin2_eq {x y z : Fin 2} (h1 : x ≠ y) (h2 : y ≠ z) : x = z := by
  revert h1 h2
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

def simple_graph_leap_group_bipartite_ne_top_preserves_or_swaps {V : Type*} (c : V → Fin 2) (g : Equiv.Perm V) : Prop :=
  (∀ v, c (g v) = c v) ∨ (∀ v, c (g v) ≠ c v)

def simple_graph_leap_group_bipartite_ne_top_subgroup {V : Type*} (c : V → Fin 2) : Subgroup (Equiv.Perm V) where
  carrier := {g | simple_graph_leap_group_bipartite_ne_top_preserves_or_swaps c g}
  one_mem' := Or.inl fun _ => rfl
  mul_mem' := by
    intro a b ha hb
    dsimp [simple_graph_leap_group_bipartite_ne_top_preserves_or_swaps] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · left; intro v; rw [ha, hb]
    · right; intro v; rw [ha]; exact hb v
    · right; intro v; rw [← hb v]; exact ha (b v)
    · left; intro v; exact simple_graph_leap_group_bipartite_ne_top_fin2_eq (ha (b v)) (hb v)
  inv_mem' := by
    intro a ha
    dsimp [simple_graph_leap_group_bipartite_ne_top_preserves_or_swaps] at ha ⊢
    rcases ha with ha | ha
    · left; intro v; have := ha (a.symm v); rw [a.apply_symm_apply] at this; exact this.symm
    · right; intro v; have := ha (a.symm v); rw [a.apply_symm_apply] at this; exact Ne.symm this

lemma simple_graph_leap_group_bipartite_ne_top_leap_group_le {V : Type*} (G : SimpleGraph V) (c : G.Coloring (Fin 2)) :
    simple_graph_leap_group G ≤ simple_graph_leap_group_bipartite_ne_top_subgroup c := by
  rw [simple_graph_leap_group, Subgroup.closure_le]
  rintro h (hh : simple_graph_is_hop G h)
  dsimp [simple_graph_leap_group_bipartite_ne_top_subgroup, simple_graph_leap_group_bipartite_ne_top_preserves_or_swaps]
  right
  intro v
  exact (c.valid (hh v)).symm

lemma simple_graph_leap_group_bipartite_ne_top_swap_not_mem {V : Type*} [DecidableEq V]
    (c : V → Fin 2) {u v w : V}
    (huv : c u ≠ c v) (hwu : w ≠ u) (hwv : w ≠ v) :
    Equiv.swap u v ∉ simple_graph_leap_group_bipartite_ne_top_subgroup c := by
  intro h
  dsimp [simple_graph_leap_group_bipartite_ne_top_subgroup, simple_graph_leap_group_bipartite_ne_top_preserves_or_swaps] at h
  rcases h with h_pres | h_swap
  · have h1 := h_pres u
    rw [Equiv.swap_apply_left] at h1
    exact huv h1.symm
  · have h2 := h_swap w
    rw [Equiv.swap_apply_of_ne_of_ne hwu hwv] at h2
    exact h2 rfl

lemma simple_graph_leap_group_bipartite_ne_top_exists_ne_pair {V : Type*} [Fintype V] [DecidableEq V]
    (h_card : 3 ≤ Fintype.card V) (u v : V) :
    ∃ w : V, w ≠ u ∧ w ≠ v := by
  by_contra! h
  have h_univ : (Finset.univ : Finset V) ⊆ {u, v} := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hx : x = u
    · left; exact hx
    · right; exact h x hx
  have h_le := Finset.card_le_card h_univ
  have h_two : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ] at h_le
  omega

/-- A bipartite graph on at least 4 vertices cannot have full leap group. -/
theorem simple_graph_leap_group_bipartite_ne_top
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h_card : 4 ≤ Fintype.card V)
    (h_bip : G.IsBipartite) :
    simple_graph_leap_group G ≠ ⊤ := by
  by_cases h_hop : ∃ h, simple_graph_is_hop G h
  · obtain ⟨h0, hh0⟩ := h_hop
    obtain ⟨c⟩ := h_bip
    have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    inhabit V
    let u : V := default
    let v : V := h0 u
    have huv : c u ≠ c v := c.valid (hh0 u)
    obtain ⟨w, hwu, hwv⟩ := simple_graph_leap_group_bipartite_ne_top_exists_ne_pair (by omega) u v
    have h_not_mem := simple_graph_leap_group_bipartite_ne_top_swap_not_mem c huv hwu hwv
    have h_le := simple_graph_leap_group_bipartite_ne_top_leap_group_le G c
    intro h_top
    have : Equiv.swap u v ∈ simple_graph_leap_group G := by
      rw [h_top]
      exact Subgroup.mem_top _
    exact h_not_mem (h_le this)
  · intro h_top
    have h_set : {h : Equiv.Perm V | simple_graph_is_hop G h} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro h hh
      exact h_hop ⟨h, hh⟩
    have h_bot : simple_graph_leap_group G = ⊥ := by
      dsimp [simple_graph_leap_group]
      rw [h_set, Subgroup.closure_empty]
    rw [h_bot] at h_top
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    have h_mem : Equiv.swap x y ∈ (⊥ : Subgroup (Equiv.Perm V)) := by
      rw [h_top]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_bot] at h_mem
    have h_app := Equiv.ext_iff.1 h_mem x
    rw [Equiv.swap_apply_left] at h_app
    change y = x at h_app
    exact hxy h_app.symm
