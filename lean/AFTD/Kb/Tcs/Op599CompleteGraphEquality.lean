import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet

/-!
# op_599_complete_graph_equality

Topic: graphs   Node: 7a5d10aad22a

Provenance: helper lemma. knowledge base, OP-599

For the complete graph on at least 1 vertex and any real lambda >= 1, the lambda-weighted mean order of a nonempty connected induced vertex set equals n * lambda * (1 + lambda)^(n - 1) / ((1 + lambda)^n - 1).
-/

open scoped BigOperators Polynomial Classical

lemma op_599_complete_graph_equality_connected_iff {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    is_connected_vertex_set (⊤ : SimpleGraph V) (↑S : Set V) ↔ S ≠ ∅ := by
  dsimp [is_connected_vertex_set]
  rw [SimpleGraph.induce_top]
  constructor
  · intro h rfl
    have hne : Nonempty (↑(∅ : Finset V) : Set V) := h.nonempty
    rw [Finset.coe_empty] at hne
    exact Set.not_nonempty_empty (Set.nonempty_coe_sort.mp hne)
  · intro hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have : Nonempty (↑S : Set V) := ⟨⟨x, hx⟩⟩
    exact SimpleGraph.connected_top

lemma op_599_complete_graph_equality_filter_eq {V : Type*} [Fintype V] [DecidableEq V] :
    (Finset.univ.filter (fun (S : Finset V) => is_connected_vertex_set (⊤ : SimpleGraph V) (↑S : Set V))) =
    Finset.univ.erase ∅ := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
  rw [op_599_complete_graph_equality_connected_iff]
  tauto

lemma op_599_complete_graph_equality_Z_eq {V : Type*} [Fintype V] [DecidableEq V] :
    (∑ S ∈ (Finset.univ.filter (fun (S : Finset V) => is_connected_vertex_set (⊤ : SimpleGraph V) (↑S : Set V))),
      (Polynomial.X : Polynomial ℝ) ^ Finset.card S) =
    (Polynomial.X + 1) ^ Fintype.card V - 1 := by
  rw [op_599_complete_graph_equality_filter_eq]
  have h_add := Finset.add_sum_erase (Finset.univ : Finset (Finset V))
    (fun S => (Polynomial.X : Polynomial ℝ) ^ S.card) (Finset.mem_univ ∅)
  have h_pow := @Fintype.sum_pow_mul_eq_add_pow (Polynomial ℝ) _ V _ (Polynomial.X : Polynomial ℝ) 1
  simp only [one_pow, mul_one] at h_pow
  simp only [Finset.card_empty, pow_zero] at h_add
  rw [← h_pow, ← h_add, add_sub_cancel_left]

open scoped BigOperators Polynomial in
/-- The complete graph achieves equality in the activity-weighted mean order bound. -/
theorem op_599_complete_graph_equality
    {V : Type*} [Fintype V] [DecidableEq V] (lam : ℝ) (hlam : 1 ≤ lam) (hn : 1 ≤ Fintype.card V) :
    let Z := open scoped Classical in
      ∑ S ∈ (Finset.univ.filter (fun (S : Finset V) => is_connected_vertex_set (⊤ : SimpleGraph V) (↑S : Set V))),
        (Polynomial.X : Polynomial ℝ) ^ Finset.card S
    let mu := (Fintype.card V : ℝ) * lam * (1 + lam) ^ (Fintype.card V - 1) / ((1 + lam) ^ (Fintype.card V) - 1)
    let mean_order := lam * (Polynomial.derivative Z).eval lam / Z.eval lam
    mean_order = mu := by
  intro Z mu mean_order
  have hZ : Z = (Polynomial.X + 1) ^ Fintype.card V - 1 := op_599_complete_graph_equality_Z_eq
  have hder : Polynomial.derivative Z =
      Polynomial.C (Fintype.card V : ℝ) * (Polynomial.X + 1) ^ (Fintype.card V - 1) := by
    rw [hZ]
    simp [Polynomial.derivative_sub, Polynomial.derivative_pow, Polynomial.derivative_add,
          Polynomial.derivative_X, Polynomial.derivative_one]
  have h_eval_der : (Polynomial.derivative Z).eval lam =
      (Fintype.card V : ℝ) * (lam + 1) ^ (Fintype.card V - 1) := by
    rw [hder]
    simp
  have h_eval_Z : Z.eval lam = (lam + 1) ^ (Fintype.card V) - 1 := by
    rw [hZ]
    simp
  dsimp [mean_order, mu]
  rw [h_eval_der, h_eval_Z]
  have h1 : lam + 1 = 1 + lam := add_comm lam 1
  rw [h1]
  ring
