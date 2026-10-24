import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount

/-!
# digraph_cut_sub_cut_eq_sum_net_degree

Topic: graphs   Node: 4f3270470687

Provenance: helper lemma. arXiv:2610.21381 Section 5

For any vertex subset A in a finite digraph G, the directed cut count e(A, Aᶜ) minus e(Aᶜ, A) equals the sum over vertices v in A of the net degree d⁺(v) - d⁻(v).
-/

/-- The difference between directed cut sizes in opposite directions across a vertex subset equals the sum of net degrees over the subset. -/
theorem digraph_cut_sub_cut_eq_sum_net_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (A : Finset V) :
    ((digraph_cut_count G A Aᶜ : ℤ) - (digraph_cut_count G Aᶜ A : ℤ)) =
      ∑ v ∈ A, (((Finset.univ.filter (G.Adj v)).card : ℤ) -
        ((Finset.univ.filter fun u => G.Adj u v).card : ℤ)) := by
  open Finset in
  simp only [digraph_cut_count, card_filter]
  push_cast
  rw [Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_sub_distrib]
  have h1 : (fun x => ∑ x_1, if G.Adj x x_1 then (1 : ℤ) else 0) =
      fun x => (∑ y ∈ A, if G.Adj x y then 1 else 0) + (∑ y ∈ Aᶜ, if G.Adj x y then 1 else 0) := by
    ext x
    exact (Finset.sum_add_sum_compl A _).symm
  have h2 : (fun x => ∑ x_1, if G.Adj x_1 x then (1 : ℤ) else 0) =
      fun x => (∑ y ∈ A, if G.Adj y x then 1 else 0) + (∑ y ∈ Aᶜ, if G.Adj y x then 1 else 0) := by
    ext x
    exact (Finset.sum_add_sum_compl A _).symm
  rw [h1, h2]
  simp only [Finset.sum_add_distrib]
  have h_comm1 : (∑ x ∈ A, ∑ y ∈ A, if G.Adj y x then (1 : ℤ) else 0) =
      ∑ x ∈ A, ∑ y ∈ A, if G.Adj x y then (1 : ℤ) else 0 := Finset.sum_comm
  have h_comm2 : (∑ x ∈ A, ∑ y ∈ Aᶜ, if G.Adj y x then (1 : ℤ) else 0) =
      ∑ y ∈ Aᶜ, ∑ x ∈ A, if G.Adj y x then (1 : ℤ) else 0 := Finset.sum_comm
  rw [h_comm1, h_comm2]
  ring
