import AFTD.Prelude
import AFTD.Kb.Tcs.CompatibleLabelings
import AFTD.Kb.Tcs.EdgeArrivalProb

/-!
# edge_arrival_prob_sum

Topic: online_algorithms   Node: 826043ff559f

Provenance: helper lemma. arXiv:2611.13571, Lemma 5.1 proof

For a simple graph G on vertex set Fin n with decidable adjacency and H : Finset (Sym2 (Fin n)), if H.card < G.edgeFinset.card and 0 < compatible_labelings G H, then the sum over e : Sym2 (Fin n) of (if e ∉ H ∧ 0 < compatible_labelings G (insert e H) then edge_arrival_prob G H e else 0) equals 1.
-/

lemma edge_arrival_prob_sum_card_map_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (π : Equiv.Perm (Fin n)) :
    (G.map π.toEmbedding).edgeFinset.card = G.edgeFinset.card := by
  have := SimpleGraph.card_edgeFinset_map π.toEmbedding G
  convert this

lemma edge_arrival_prob_sum_card_filter_eq {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop) [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, (t.filter (r a ·)).card : ℕ) = ∑ b ∈ t, (s.filter (r · b)).card := by
  have h1 : ∀ a, (t.filter (r a ·)).card = ∑ b ∈ t, if r a b then 1 else 0 := by
    intro a
    rw [← Finset.sum_filter]
    simp
  have h2 : ∀ b, (s.filter (r · b)).card = ∑ a ∈ s, if r a b then 1 else 0 := by
    intro b
    rw [← Finset.sum_filter]
    simp
  simp_rw [h1, h2]
  exact Finset.sum_comm

lemma edge_arrival_prob_sum_filter_edges_diff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n)))
    (π : Equiv.Perm (Fin n)) (hH : H ⊆ (G.map π.toEmbedding).edgeFinset) :
    ((Finset.univ.filter (fun e : Sym2 (Fin n) => e ∉ H)).filter
      (fun e => e ∈ (G.map π.toEmbedding).edgeFinset)).card =
    G.edgeFinset.card - H.card := by
  have heq : ((Finset.univ.filter (fun e : Sym2 (Fin n) => e ∉ H)).filter
      (fun e => e ∈ (G.map π.toEmbedding).edgeFinset)) =
    (G.map π.toEmbedding).edgeFinset \ H := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    tauto
  rw [heq, Finset.card_sdiff_of_subset hH, edge_arrival_prob_sum_card_map_edges]

lemma edge_arrival_prob_sum_compatible_labelings_insert {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n))) :
    ∑ e ∈ Finset.univ.filter (fun e : Sym2 (Fin n) => e ∉ H), compatible_labelings G (insert e H) =
    (G.edgeFinset.card - H.card) * compatible_labelings G H := by
  let P := Finset.univ.filter (fun π : Equiv.Perm (Fin n) => H ⊆ (G.map π.toEmbedding).edgeFinset)
  have h1 : ∀ e, compatible_labelings G (insert e H) =
      (P.filter (fun π => e ∈ (G.map π.toEmbedding).edgeFinset)).card := by
    intro e
    unfold compatible_labelings
    apply congr_arg Finset.card
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff, P]
    tauto
  simp_rw [h1]
  rw [edge_arrival_prob_sum_card_filter_eq]
  have h2 : ∀ π ∈ P,
      ((Finset.univ.filter (fun e : Sym2 (Fin n) => e ∉ H)).filter
        (fun e => e ∈ (G.map π.toEmbedding).edgeFinset)).card =
      G.edgeFinset.card - H.card := by
    intro π hπ
    have hH : H ⊆ (G.map π.toEmbedding).edgeFinset := (Finset.mem_filter.mp hπ).2
    exact edge_arrival_prob_sum_filter_edges_diff G H π hH
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  change P.card * (G.edgeFinset.card - H.card) = (G.edgeFinset.card - H.card) * compatible_labelings G H
  have : compatible_labelings G H = P.card := rfl
  rw [this, mul_comm]

lemma edge_arrival_prob_sum_summand_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n)))
    (hcard : H.card < G.edgeFinset.card)
    (hcomp : 0 < compatible_labelings G H)
    (e : Sym2 (Fin n)) :
    (if e ∉ H ∧ 0 < compatible_labelings G (insert e H) then edge_arrival_prob G H e else 0) =
    if e ∉ H then (compatible_labelings G (insert e H) : ℝ) /
      ((G.edgeFinset.card - H.card : ℝ) * (compatible_labelings G H : ℝ)) else 0 := by
  have hd : ((G.edgeFinset.card - H.card : ℝ) * (compatible_labelings G H : ℝ)) ≠ 0 := by
    have h1 : (G.edgeFinset.card - H.card : ℝ) ≠ 0 := by
      have : (H.card : ℝ) < G.edgeFinset.card := Nat.cast_lt.mpr hcard
      linarith
    have h2 : (compatible_labelings G H : ℝ) ≠ 0 := by
      have : 0 < (compatible_labelings G H : ℝ) := Nat.cast_pos.mpr hcomp
      linarith
    exact mul_ne_zero h1 h2
  unfold edge_arrival_prob
  rw [if_neg hd]
  by_cases he : e ∈ H
  · rw [if_neg (fun h => h.1 he), if_neg (fun h => h he)]
  · rw [if_pos he]
    by_cases hc : 0 < compatible_labelings G (insert e H)
    · rw [if_pos ⟨he, hc⟩]
    · rw [if_neg (fun h => hc h.2)]
      have : compatible_labelings G (insert e H) = 0 := by omega
      rw [this, Nat.cast_zero, zero_div]

/-- Edge arrival transition probabilities sum to 1 over remaining edges. -/
theorem edge_arrival_prob_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n)))
    (hcard : H.card < G.edgeFinset.card)
    (hcomp : 0 < compatible_labelings G H) :
    ∑ e ∈ (Finset.univ : Finset (Sym2 (Fin n))),
      (if e ∉ H ∧ 0 < compatible_labelings G (insert e H) then edge_arrival_prob G H e else 0) = 1 := by
  have hd : ((G.edgeFinset.card - H.card : ℝ) * (compatible_labelings G H : ℝ)) ≠ 0 := by
    have h1 : (G.edgeFinset.card - H.card : ℝ) ≠ 0 := by
      have : (H.card : ℝ) < G.edgeFinset.card := Nat.cast_lt.mpr hcard
      linarith
    have h2 : (compatible_labelings G H : ℝ) ≠ 0 := by
      have : 0 < (compatible_labelings G H : ℝ) := Nat.cast_pos.mpr hcomp
      linarith
    exact mul_ne_zero h1 h2
  simp_rw [edge_arrival_prob_sum_summand_eq G H hcard hcomp]
  rw [← Finset.sum_filter, ← Finset.sum_div, ← Nat.cast_sum]
  rw [edge_arrival_prob_sum_compatible_labelings_insert G H]
  push_cast
  rw [Nat.cast_sub (le_of_lt hcard)]
  exact div_self hd
