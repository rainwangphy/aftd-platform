import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeMaxCliqueOrder

/-!
# op_2282_turan_graph_sum_eq_one

Topic: graphs   Node: 9138fd488688

Provenance: formalization of a published result. Source: arXiv:2611.30029 after Theorem 1.4

For any natural numbers n and s with 2 ≤ s ≤ n, the Turán graph T_s(n) satisfies the equality that the sum over all its edges e of 1 / |E(T_{w(e)}(n))| equals 1.
-/

def op_2282_turan_clique_vertex (n s : ℕ) (hsn : s ≤ n) (u v : Fin n) (i : Fin s) : Fin n :=
  if i.1 = u.1 % s then u
  else if i.1 = v.1 % s then v
  else ⟨i.1, i.isLt.trans_le hsn⟩

lemma op_2282_turan_clique_vertex_mod (n s : ℕ) (hsn : s ≤ n) (u v : Fin n) (i : Fin s) :
    (op_2282_turan_clique_vertex n s hsn u v i).1 % s = i.1 := by
  dsimp [op_2282_turan_clique_vertex]
  split_ifs with h1 h2
  · exact h1.symm
  · exact h2.symm
  · exact Nat.mod_eq_of_lt i.isLt

lemma op_2282_turan_clique_vertex_inj (n s : ℕ) (hsn : s ≤ n) (u v : Fin n) :
    Function.Injective (op_2282_turan_clique_vertex n s hsn u v) := by
  intro i j hij
  have h := congr_arg (fun (x : Fin n) => x.1 % s) hij
  rw [op_2282_turan_clique_vertex_mod, op_2282_turan_clique_vertex_mod] at h
  exact Fin.ext h

theorem op_2282_turan_edge_max_clique_order_eq (n s : ℕ) (hs2 : 2 ≤ s) (hsn : s ≤ n)
    {e : Sym2 (Fin n)} (he : e ∈ (SimpleGraph.turanGraph n s).edgeFinset) :
    edge_max_clique_order (SimpleGraph.turanGraph n s) e = s := by
  induction' e using Sym2.ind with u v
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.turanGraph_adj] at he
  have hs_pos : 0 < s := by omega
  have hle : edge_max_clique_order (SimpleGraph.turanGraph n s) s(u, v) ≤ s := by
    have hcf := SimpleGraph.turanGraph_cliqueFree (n := n) hs_pos
    dsimp [edge_max_clique_order]
    classical
    apply Finset.sup_le
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    by_contra! h
    obtain ⟨w, hw_sub, hw_card⟩ := Finset.exists_subset_card_eq h
    have hw_clique : (SimpleGraph.turanGraph n s).IsClique (w : Set (Fin n)) :=
      Set.Pairwise.mono (Finset.coe_subset.mpr hw_sub) ht.1
    exact hcf w ⟨hw_clique, hw_card⟩
  have hge : s ≤ edge_max_clique_order (SimpleGraph.turanGraph n s) s(u, v) := by
    let f := op_2282_turan_clique_vertex n s hsn u v
    let K : Finset (Fin n) := Finset.univ.image f
    have hcard : K.card = s := by
      rw [Finset.card_image_of_injective _ (op_2282_turan_clique_vertex_inj n s hsn u v),
        Finset.card_univ, Fintype.card_fin]
    have hclique : (SimpleGraph.turanGraph n s).IsClique (K : Set (Fin n)) := by
      intro x hx y hy hne
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨i, -, rfl⟩ := hx
      obtain ⟨j, -, rfl⟩ := hy
      rw [SimpleGraph.turanGraph_adj, op_2282_turan_clique_vertex_mod, op_2282_turan_clique_vertex_mod]
      intro hij
      apply hne
      exact congr_arg f (Fin.ext hij)
    have hsub : (s(u, v) : Sym2 (Fin n)).toFinset ⊆ K := by
      rw [Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_image]
        refine ⟨⟨u.1 % s, Nat.mod_lt _ hs_pos⟩, Finset.mem_univ _, ?_⟩
        dsimp [f, op_2282_turan_clique_vertex]
        exact if_pos rfl
      · rw [Finset.mem_image]
        refine ⟨⟨v.1 % s, Nat.mod_lt _ hs_pos⟩, Finset.mem_univ _, ?_⟩
        dsimp [f, op_2282_turan_clique_vertex]
        rw [if_neg (Ne.symm he)]
        exact if_pos rfl
    have hsup : K.card ≤ edge_max_clique_order (SimpleGraph.turanGraph n s) s(u, v) := by
      dsimp [edge_max_clique_order]
      classical
      refine Finset.le_sup (f := Finset.card) ?_
      simp [hclique, hsub]
    rwa [hcard] at hsup
  exact le_antisymm hle hge

lemma op_2282_turan_edgeFinset_nonempty (n s : ℕ) (hs2 : 2 ≤ s) (hsn : s ≤ n) :
    (SimpleGraph.turanGraph n s).edgeFinset.Nonempty := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  let u : Fin n := ⟨0, h0⟩
  let v : Fin n := ⟨1, h1⟩
  have hadj : (SimpleGraph.turanGraph n s).Adj u v := by
    rw [SimpleGraph.turanGraph_adj]
    dsimp [u, v]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact zero_ne_one
  refine ⟨s(u, v), ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact hadj

/-- Every Turan graph T_s(n) achieves equality in the exact edge-localized Turan inequality. -/
theorem op_2282_turan_graph_sum_eq_one
    (n s : ℕ) (hn : 2 ≤ n) (hs2 : 2 ≤ s) (hsn : s ≤ n) :
    ∑ e ∈ (SimpleGraph.turanGraph n s).edgeFinset,
      (1 : ℝ) / (SimpleGraph.turanGraph n (edge_max_clique_order (SimpleGraph.turanGraph n s) e)).edgeFinset.card = 1 := by
  have _ := hn
  have h_eq : ∀ e ∈ (SimpleGraph.turanGraph n s).edgeFinset,
      (1 : ℝ) / (SimpleGraph.turanGraph n (edge_max_clique_order (SimpleGraph.turanGraph n s) e)).edgeFinset.card =
      (1 : ℝ) / (SimpleGraph.turanGraph n s).edgeFinset.card := by
    intro e he
    rw [op_2282_turan_edge_max_clique_order_eq n s hs2 hsn he]
  rw [Finset.sum_congr rfl h_eq]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hne : (SimpleGraph.turanGraph n s).edgeFinset.card ≠ 0 :=
    (op_2282_turan_edgeFinset_nonempty n s hs2 hsn).card_pos.ne'
  have hne_real : ((SimpleGraph.turanGraph n s).edgeFinset.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hne
  exact mul_one_div_cancel hne_real
