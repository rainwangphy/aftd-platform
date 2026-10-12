import AFTD.Prelude

/-!
# simple_graph_exists_matching_labeling_card_edgeFinset_le_two_mul_arcs_add

Topic: combinatorics   Node: 5c7e4d60d628

Provenance: formalization of a published result. Source: arXiv:2610.11441 (Spanning Even Linear Forests with Isolated Edges Share the Anti-Ramsey Numbers of Perfect Matchings), Claim 3.2 (first inequality a(D) ≥ (q−s)/2; the comparison with the anti-Ramsey number is not part of it). Stated in ℕ as q ≤ 2a(D) + s; the vertex set is covered by the s matching edges.

Let G be a simple graph on 2s vertices with q edges and a perfect matching M = {u_i v_i : 1 ≤ i ≤ s}. For an endpoint labeling (a_i,b_i) ∈ {(u_i,v_i),(v_i,u_i)}, let D be the digraph on {1,…,s} with i → j iff i ≠ j and b_i a_j ∈ E(G). Some labeling has a(D) ≥ (q − s)/2 arcs, i.e. q ≤ 2·a(D) + s. In the Lean, σ i = true means (a_i,b_i) = (u_i,v_i).
-/

theorem simple_graph_exists_matching_labeling_card_edgeFinset_le_two_mul_arcs_add
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ)
    (u v : Fin s → V) (hM : ∀ i, G.Adj (u i) (v i)) (hu : Function.Injective u)
    (hv : Function.Injective v) (huv : ∀ i j, u i ≠ v j) (hcover : ∀ x, ∃ i, x = u i ∨ x = v i) :
    ∃ σ : Fin s → Bool, G.edgeFinset.card ≤
      2 * (Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 ≠ ij.2 ∧
        G.Adj (if σ ij.1 then v ij.1 else u ij.1) (if σ ij.2 then u ij.2 else v ij.2))).card + s := by
  classical
  -- adjacency indicator
  let f : V → V → ℕ := fun x y => if G.Adj x y then 1 else 0
  have fsymm : ∀ x y, f x y = f y x := fun x y => by simp only [f, G.adj_comm]
  -- labels
  let a : (Fin s → Bool) → Fin s → V := fun σ i => if σ i then u i else v i
  let b : (Fin s → Bool) → Fin s → V := fun σ i => if σ i then v i else u i
  let g : (Fin s → Bool) → Fin s → Fin s → ℕ := fun σ k l => if k ≠ l then f (b σ k) (a σ l) else 0
  let A : (Fin s → Bool) → ℕ := fun σ => ∑ k, ∑ l, g σ k l
  have hA : ∀ σ, (Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 ≠ ij.2 ∧
      G.Adj (if σ ij.1 then v ij.1 else u ij.1) (if σ ij.2 then u ij.2 else v ij.2))).card = A σ := by
    intro σ
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [g, f, a, b]
    by_cases hkl : k = l <;> simp [hkl]
  simp_rw [hA]
  -- cross edges between pairs
  let e : Fin s → Fin s → ℕ := fun i j => f (u i) (u j) + f (u i) (v j) + f (v i) (u j) + f (v i) (v j)
  -- R σ i: arcs at i
  let R : (Fin s → Bool) → Fin s → ℕ := fun σ i => ∑ l, g σ i l + ∑ k, g σ k i
  have hg_self : ∀ σ k, g σ k k = 0 := fun σ k => by simp [g]
  -- decomposition A σ = rest + R σ i
  let rest : (Fin s → Bool) → Fin s → ℕ := fun σ i =>
    ∑ k, ∑ l, if k ≠ i ∧ l ≠ i then g σ k l else 0
  have hdecomp : ∀ σ i, A σ = rest σ i + R σ i := by
    intro σ i
    simp only [A, rest, R]
    have : ∀ k l, g σ k l = (if k ≠ i ∧ l ≠ i then g σ k l else 0) +
        ((if k = i then g σ k l else 0) + (if l = i then g σ k l else 0)) := by
      intro k l
      by_cases hk : k = i <;> by_cases hl : l = i
      · subst hk; subst hl; simp [hg_self]
      · simp [hk, hl]
      · simp [hk, hl]
      · simp [hk, hl]
    conv_lhs => enter [2, k, 2, l]; rw [this k l]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hrow_i : (∑ x, ∑ l, if x = i then g σ x l else 0) = ∑ l, g σ i l := by
      rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
      simp
    rw [hrow_i]
  -- flipping i does not change rest
  let flip : (Fin s → Bool) → Fin s → (Fin s → Bool) := fun σ i => Function.update σ i (!σ i)
  have hrest : ∀ σ i, rest (flip σ i) i = rest σ i := by
    intro σ i
    simp only [rest]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases h : k ≠ i ∧ l ≠ i
    · simp only [h, ne_eq, not_false_eq_true, and_self, if_true, g, a, b, flip,
        Function.update_of_ne h.1, Function.update_of_ne h.2]
    · simp [h]
  -- R (flip σ i) i + R σ i = ∑_{l ≠ i} e i l
  have hRsum : ∀ σ i, R (flip σ i) i + R σ i = ∑ l, if l ≠ i then e i l else 0 := by
    intro σ i
    simp only [R]
    rw [add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [hg_self]
    · have hli : i ≠ l := Ne.symm hl
      simp only [g, a, b, flip, ne_eq, hli, hl, not_false_eq_true, if_true,
        Function.update_self, Function.update_of_ne hl]
      cases σ i <;> cases σ l <;> simp [e, fsymm] <;> omega
  -- totals
  have hRtot : ∀ σ, ∑ i, R σ i = 2 * A σ := by
    intro σ
    simp only [R, A, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i k => g σ k i)]
    ring
  have hreidx : ∀ h : V → ℕ, ∑ y, h y = ∑ j, (h (u j) + h (v j)) := by
    intro h
    have hbij : Function.Bijective (Sum.elim u v) := by
      constructor
      · rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
        · rw [hu hij]
        · exact absurd hij (huv i j)
        · exact absurd hij.symm (huv j i)
        · rw [hv hij]
      · intro x
        obtain ⟨i, h | h⟩ := hcover x
        · exact ⟨Sum.inl i, h.symm⟩
        · exact ⟨Sum.inr i, h.symm⟩
    rw [← (Equiv.ofBijective _ hbij).sum_comp, Fintype.sum_sum_type, Finset.sum_add_distrib]
    simp
  have hdeg : ∀ x, G.degree x = ∑ y, f x y := by
    intro x
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter]
  have hii : ∀ i, e i i = 2 := fun i => by
    simp [e, f, hM i, (hM i).symm]
  have hrow : ∀ i, ∑ j, e i j = 2 + ∑ l, if l ≠ i then e i l else 0 := by
    intro i
    have : ∀ j, e i j = (if j ≠ i then e i j else 0) + (if j = i then e i j else 0) := by
      intro j
      by_cases hj : j = i <;> simp [hj]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [hii, add_comm]
  have hE : 2 * G.edgeFinset.card = 2 * s + ∑ i, ∑ l, if l ≠ i then e i l else 0 := by
    have h2 := G.sum_degrees_eq_twice_card_edges
    simp_rw [hdeg] at h2
    calc 2 * G.edgeFinset.card = ∑ x, ∑ y, f x y := h2.symm
      _ = ∑ i, ∑ j, e i j := by
          rw [hreidx (fun x => ∑ y, f x y)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hreidx (f (u i)), hreidx (f (v i)), ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [e]
          ring
      _ = ∑ i, (2 + ∑ l, if l ≠ i then e i l else 0) := Finset.sum_congr rfl fun i _ => hrow i
      _ = 2 * s + ∑ i, ∑ l, if l ≠ i then e i l else 0 := by
          rw [Finset.sum_add_distrib]
          simp [mul_comm]
  -- choose a maximiser
  obtain ⟨σ, -, hmax⟩ := Finset.exists_max_image Finset.univ A Finset.univ_nonempty
  refine ⟨σ, ?_⟩
  have hloc : ∀ i, (∑ l, if l ≠ i then e i l else 0) ≤ 2 * R σ i := by
    intro i
    have h1 := hmax (flip σ i) (Finset.mem_univ _)
    rw [hdecomp (flip σ i) i, hdecomp σ i, hrest] at h1
    have h2 := hRsum σ i
    omega
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hloc i
  rw [← Finset.mul_sum, hRtot] at hsum
  omega
