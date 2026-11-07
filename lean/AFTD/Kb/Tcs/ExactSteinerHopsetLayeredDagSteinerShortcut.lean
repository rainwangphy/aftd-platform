import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsHead
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesWithinStepsRefl
import AFTD.Kb.Tcs.RelationRelatesInStepsMap
import AFTD.Kb.Tcs.RelationRelatesWithinStepsMap

/-!
# exact_steiner_hopset_layered_dag_steiner_shortcut

Topic: graphs   Node: 4cea866fc228

Provenance: formalization of a published result. Source: arXiv:2611.07043 (Polynomial Lower Bounds for Steiner Shortcuts via Test Functions), Lemma 4.2. The hopset's distance conditions are stated through walks (every H-walk between original vertices weighs at least dist_G, and connected pairs have a walk of weight dist_G with at most β edges), which is equivalent to dist_H = dist_G on V plus the hopbound, without infinite distances. Proof differs slightly from the paper's: the extended layering is the infimum of ℓ(u) + weight over all walks from original vertices (0 for vertices not connected to V), so no shortest path or vertex deletion is needed.

Let V and W be finite types, Gv a directed graph on V and ℓ : V → ℕ a layering such that every arc u → v of Gv has ℓ v = ℓ u + 1 (a layered DAG), and let G be its undirected version (u, v adjacent iff u ≠ v and u → v or v → u). Let H be a simple graph on V ⊕ W (W the Steiner vertices) containing the copy of G on V, with edge weights w that are positive on the edges of H and equal to 1 on the edges of G, forming an exact Steiner hopset of G with hopbound β: every walk in H between original vertices s, t has weight at least the distance dist_G(s, t) (in particular s and t are connected in G), and every pair s, t connected in G is joined by a walk in H of weight exactly dist_G(s, t) with at most β edges. Then there is a directed graph Hv on V ⊕ W containing every arc of Gv (on V) such that the number of arcs of Hv that are not arcs of Gv is at most the number of edges of H not in the copy of G, for original vertices x, y, x reaches y in Hv iff x reaches y in Gv, and whenever x reaches y in Gv, x reaches y in Hv in at most β steps.
-/

theorem steiner_hopset_layer_diff_le_length {V : Type*} (Gv : Digraph V) (ℓ : V → ℕ)
    (hℓ : ∀ u v, Gv.Adj u v → ℓ v = ℓ u + 1) {u x : V}
    (q : (SimpleGraph.fromRel Gv.Adj).Walk u x) :
    |(ℓ x : ℤ) - ℓ u| ≤ q.length := by
  induction q with
  | nil => simp
  | @cons a b c h q ih =>
    rw [SimpleGraph.fromRel_adj] at h
    rw [SimpleGraph.Walk.length_cons]
    rw [abs_le] at ih ⊢
    rcases h.2 with h' | h'
    · have := hℓ _ _ h'; push_cast; constructor <;> omega
    · have := hℓ _ _ h'; push_cast; constructor <;> omega

theorem steiner_hopset_walk_directed_of_length_le {V : Type*} (Gv : Digraph V) (ℓ : V → ℕ)
    (hℓ : ∀ u v, Gv.Adj u v → ℓ v = ℓ u + 1) {u x : V}
    (q : (SimpleGraph.fromRel Gv.Adj).Walk u x) (hq : (q.length : ℤ) ≤ (ℓ x : ℤ) - ℓ u) :
    Relation.ReflTransGen Gv.Adj u x := by
  induction q with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c h q ih =>
    rw [SimpleGraph.fromRel_adj] at h
    rw [SimpleGraph.Walk.length_cons] at hq
    have hb := steiner_hopset_layer_diff_le_length Gv ℓ hℓ q
    rw [abs_le] at hb
    rcases h.2 with h' | h'
    · have := hℓ _ _ h'
      exact Relation.ReflTransGen.head h' (ih (by push_cast at hq; omega))
    · have := hℓ _ _ h'
      push_cast at hq
      omega

theorem steiner_hopset_walk_of_directed {V : Type*} (Gv : Digraph V) (ℓ : V → ℕ)
    (hℓ : ∀ u v, Gv.Adj u v → ℓ v = ℓ u + 1) {x y : V}
    (h : Relation.ReflTransGen Gv.Adj x y) :
    ∃ q : (SimpleGraph.fromRel Gv.Adj).Walk x y, (q.length : ℤ) = (ℓ y : ℤ) - ℓ x := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨q, hq⟩ := ih
    have hl := hℓ _ _ hbc
    have hadj : (SimpleGraph.fromRel Gv.Adj).Adj b c := by
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl hbc⟩
      rintro rfl; omega
    refine ⟨q.concat hadj, ?_⟩
    rw [SimpleGraph.Walk.length_concat]
    push_cast; omega

theorem exact_steiner_hopset_layered_dag_steiner_shortcut
    {V W : Type*} [Finite V] [Finite W]
    (Gv : Digraph V) (ℓ : V → ℕ) (hℓ : ∀ u v, Gv.Adj u v → ℓ v = ℓ u + 1)
    (H : SimpleGraph (V ⊕ W)) (w : Sym2 (V ⊕ W) → ℝ) (β : ℕ)
    (hGH : (SimpleGraph.fromRel Gv.Adj).map Function.Embedding.inl ≤ H)
    (hw1 : ∀ u v, (SimpleGraph.fromRel Gv.Adj).Adj u v → w s(Sum.inl u, Sum.inl v) = 1)
    (hwpos : ∀ e ∈ H.edgeSet, 0 < w e)
    (hdist : ∀ s t (p : H.Walk (Sum.inl s) (Sum.inl t)),
      (SimpleGraph.fromRel Gv.Adj).Reachable s t ∧
        ((SimpleGraph.fromRel Gv.Adj).dist s t : ℝ) ≤ (p.edges.map w).sum)
    (hhop : ∀ s t, (SimpleGraph.fromRel Gv.Adj).Reachable s t →
      ∃ p : H.Walk (Sum.inl s) (Sum.inl t),
        (p.edges.map w).sum = (SimpleGraph.fromRel Gv.Adj).dist s t ∧ p.length ≤ β) :
    ∃ Hv : Digraph (V ⊕ W),
      (∀ u v, Gv.Adj u v → Hv.Adj (Sum.inl u) (Sum.inl v)) ∧
      {x : (V ⊕ W) × (V ⊕ W) | Hv.Adj x.1 x.2 ∧ ¬ ∃ u v, x = (Sum.inl u, Sum.inl v) ∧ Gv.Adj u v}.ncard ≤
        (H.edgeSet \ ((SimpleGraph.fromRel Gv.Adj).map Function.Embedding.inl).edgeSet).ncard ∧
      (∀ x y : V, Relation.ReflTransGen Hv.Adj (Sum.inl x) (Sum.inl y) ↔
        Relation.ReflTransGen Gv.Adj x y) ∧
      (∀ x y : V, Relation.ReflTransGen Gv.Adj x y →
        Relation.RelatesWithinSteps Hv.Adj (Sum.inl x) (Sum.inl y) β) := by
  set G := SimpleGraph.fromRel Gv.Adj with hG
  -- weights of walks are nonnegative
  have wt_nonneg : ∀ {a b} (p : H.Walk a b), 0 ≤ (p.edges.map w).sum := by
    intro a b p
    apply List.sum_nonneg
    intro r hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    exact (hwpos e (p.edges_subset_edgeSet he)).le
  let S : V ⊕ W → Set ℝ := fun a => {r | ∃ u, ∃ p : H.Walk (Sum.inl u) a, r = ℓ u + (p.edges.map w).sum}
  have hS_bdd : ∀ a, BddBelow (S a) := by
    intro a
    refine ⟨0, ?_⟩
    rintro r ⟨u, p, rfl⟩
    have := wt_nonneg p
    positivity
  let φ : V ⊕ W → ℝ := fun a => sInf (S a)
  -- P1: potential inequality along edges
  have P1 : ∀ a b, H.Adj a b → φ b ≤ φ a + w s(a, b) := by
    intro a b hab
    by_cases hne : (S a).Nonempty
    · have : φ b - w s(a, b) ≤ φ a := by
        apply le_csInf hne
        rintro r ⟨u, p, rfl⟩
        have hmem : (ℓ u : ℝ) + ((p.concat hab).edges.map w).sum ∈ S b := ⟨u, p.concat hab, rfl⟩
        have := csInf_le (hS_bdd b) hmem
        simp only [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.map_append,
          List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
        show φ b - w s(a, b) ≤ _
        linarith
      linarith
    · have hb : ¬ (S b).Nonempty := by
        rintro ⟨r, u, p, rfl⟩
        exact hne ⟨_, u, p.concat hab.symm, rfl⟩
      rw [Set.not_nonempty_iff_eq_empty] at hne hb
      have := hwpos s(a, b) ((SimpleGraph.mem_edgeSet H).mpr hab)
      show sInf (S b) ≤ sInf (S a) + _
      rw [hne, hb, Real.sInf_empty]
      linarith
  -- P2: potential agrees with the layering on V
  have P2 : ∀ x : V, φ (Sum.inl x) = ℓ x := by
    intro x
    have hmem : (ℓ x : ℝ) + ((SimpleGraph.Walk.nil : H.Walk (Sum.inl x) (Sum.inl x)).edges.map w).sum ∈ S (Sum.inl x) :=
      ⟨x, SimpleGraph.Walk.nil, rfl⟩
    apply le_antisymm
    · have := csInf_le (hS_bdd _) hmem
      simpa using this
    · apply le_csInf ⟨_, hmem⟩
      rintro r ⟨u, p, rfl⟩
      obtain ⟨hr, hd⟩ := hdist u x p
      obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
      have hl := steiner_hopset_layer_diff_le_length Gv ℓ hℓ q
      rw [abs_le, hq] at hl
      have h1 : (ℓ x : ℝ) - ℓ u ≤ (G.dist u x : ℝ) := by exact_mod_cast hl.2
      linarith
  -- lower bound along walks
  have lower : ∀ {a b} (p : H.Walk a b), φ b - φ a ≤ (p.edges.map w).sum := by
    intro a b p
    induction p with
    | nil => simp
    | @cons a c b h p ih =>
      have := P1 a c h
      simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
      linarith
  let Hv : Digraph (V ⊕ W) := { Adj := fun a b => H.Adj a b ∧ φ b - φ a = w s(a, b) }
  have C1 : ∀ u v, Gv.Adj u v → Hv.Adj (Sum.inl u) (Sum.inl v) := by
    intro u v huv
    have hl := hℓ u v huv
    have hGuv : G.Adj u v := by
      rw [hG, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl huv⟩
      rintro rfl; omega
    refine ⟨hGH ?_, ?_⟩
    · rw [SimpleGraph.map_adj]
      exact ⟨u, v, hGuv, rfl, rfl⟩
    · show φ (Sum.inl v) - φ (Sum.inl u) = _
      rw [P2, P2, hw1 u v hGuv, hl]
      push_cast; ring
  have walk_of_Hv : ∀ {a b}, Relation.ReflTransGen Hv.Adj a b →
      ∃ p : H.Walk a b, (p.edges.map w).sum = φ b - φ a := by
    intro a b h
    induction h with
    | refl => exact ⟨SimpleGraph.Walk.nil, by simp⟩
    | @tail b c _ hbc ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.concat hbc.1, ?_⟩
      simp only [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := hbc.2
      linarith
  have tight : ∀ {a b} (p : H.Walk a b), (p.edges.map w).sum ≤ φ b - φ a →
      Relation.RelatesInSteps Hv.Adj a b p.length := by
    intro a b p
    induction p with
    | nil => intro _; exact Relation.RelatesInSteps.refl _
    | @cons a c b h p ih =>
      intro hp
      simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons] at hp
      have h1 := P1 a c h
      have h2 := lower p
      rw [SimpleGraph.Walk.length_cons]
      refine Relation.RelatesInSteps.head _ _ _ _ ⟨h, ?_⟩ (ih (by linarith))
      linarith
  refine ⟨Hv, C1, ?_, ?_, ?_⟩
  · -- counting the added edges
    apply Set.ncard_le_ncard_of_injOn (fun x => s(x.1, x.2))
    · rintro ⟨a, b⟩ ⟨⟨hab, hφ⟩, hnot⟩
      refine ⟨(SimpleGraph.mem_edgeSet H).mpr hab, ?_⟩
      intro hmem
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at hmem
      obtain ⟨u, v, huv, rfl, rfl⟩ := hmem
      have huv' := huv
      rw [hG, SimpleGraph.fromRel_adj] at huv'
      rcases huv'.2 with h' | h'
      · exact hnot ⟨u, v, rfl, h'⟩
      · have hl := hℓ _ _ h'
        have hw := hw1 u v huv
        change φ (Sum.inl v) - φ (Sum.inl u) = w s(Sum.inl u, Sum.inl v) at hφ
        rw [P2, P2, hw, hl] at hφ
        push_cast at hφ
        linarith
    · rintro ⟨a, b⟩ ⟨⟨hab, hφ⟩, _⟩ ⟨c, d⟩ ⟨⟨hcd, hφ'⟩, _⟩ heq
      simp only [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · have := hwpos s(a, b) ((SimpleGraph.mem_edgeSet H).mpr hab)
        simp only at hφ hφ'
        rw [Sym2.eq_swap] at hφ'
        linarith
  · intro x y
    constructor
    · intro h
      obtain ⟨p, hp⟩ := walk_of_Hv h
      obtain ⟨hr, hd⟩ := hdist x y p
      rw [hp, P2, P2] at hd
      obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
      apply steiner_hopset_walk_directed_of_length_le Gv ℓ hℓ q
      rw [hq]
      exact_mod_cast hd
    · intro h
      exact h.lift Sum.inl C1
  · intro x y h
    obtain ⟨q, hq⟩ := steiner_hopset_walk_of_directed Gv ℓ hℓ h
    have hr : G.Reachable x y := ⟨q⟩
    obtain ⟨p, hpw, hpl⟩ := hhop x y hr
    obtain ⟨q', hq'⟩ := hr.exists_walk_length_eq_dist
    have hl := steiner_hopset_layer_diff_le_length Gv ℓ hℓ q'
    rw [abs_le, hq'] at hl
    have h1 : (ℓ y : ℝ) - ℓ x ≤ (G.dist x y : ℝ) := by exact_mod_cast hl.2
    refine ⟨p.length, hpl, tight p ?_⟩
    rw [hpw, P2, P2]
    have h2 : (G.dist x y : ℤ) ≤ (ℓ y : ℤ) - ℓ x := by
      rw [← hq]; exact_mod_cast SimpleGraph.dist_le q
    have h3 : (G.dist x y : ℝ) ≤ (ℓ y : ℝ) - ℓ x := by exact_mod_cast h2
    exact h3
