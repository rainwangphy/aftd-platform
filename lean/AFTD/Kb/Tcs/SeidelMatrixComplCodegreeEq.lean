import AFTD.Prelude
import AFTD.Kb.Tcs.SeidelMatrix
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# seidel_matrix_compl_codegree_eq

Topic: combinatorics   Node: 2006498531c8

Provenance: formalization of a published result. Source: arXiv:2610.36522 Lemma 7

For any simple graph G on a finite vertex set V with Seidel matrix S and any pair of adjacent vertices u and v in the complement Gᶜ, four times the number of common neighbors of u and v in Gᶜ equals |V| - 4 + ∑_k S_{uk} + ∑_k S_{vk} + (S^2)_{uv}.
-/

private def seidel_matrix_compl_codegree_eq_g {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) : ℤ := if G.Adj x y then -1 else 1

private lemma seidel_matrix_compl_codegree_eq_g_symm {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    seidel_matrix_compl_codegree_eq_g G x y = seidel_matrix_compl_codegree_eq_g G y x := by
  unfold seidel_matrix_compl_codegree_eq_g
  by_cases h : G.Adj x y
  · have h' : G.Adj y x := by simpa [SimpleGraph.adj_comm] using h
    simp [h, h']
  · have h' : ¬ G.Adj y x := fun hh => h (by simpa [SimpleGraph.adj_comm] using hh)
    simp [h, h']

private lemma seidel_matrix_compl_codegree_eq_entry {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    seidel_matrix G x y = seidel_matrix_compl_codegree_eq_g G x y - (if x = y then (1:ℤ) else 0) := by
  unfold seidel_matrix seidel_matrix_compl_codegree_eq_g
  by_cases h : x = y
  · subst h
    simp [SimpleGraph.irrefl]
  · simp [h]

private lemma seidel_matrix_compl_codegree_eq_row_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (∑ k : V, seidel_matrix G x k) = (∑ k : V, seidel_matrix_compl_codegree_eq_g G x k) - 1 := by
  have h : ∀ k : V, seidel_matrix G x k
      = seidel_matrix_compl_codegree_eq_g G x k - (if x = k then (1:ℤ) else 0) := by
    intro k
    rw [seidel_matrix_compl_codegree_eq_entry]
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

private lemma seidel_matrix_compl_codegree_eq_sq_entry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (hne : u ≠ v) (hna : ¬ G.Adj u v) :
    (seidel_matrix G * seidel_matrix G) u v
      = (∑ k : V, seidel_matrix_compl_codegree_eq_g G u k *
          seidel_matrix_compl_codegree_eq_g G v k) - 2 := by
  rw [Matrix.mul_apply]
  have key : ∀ k : V, seidel_matrix G u k * seidel_matrix G k v
      = seidel_matrix_compl_codegree_eq_g G u k * seidel_matrix_compl_codegree_eq_g G v k
        - (if k = u then 1 else 0) - (if k = v then 1 else 0) := by
    intro k
    have hna' : ¬ G.Adj v u := fun h => hna (by simpa [SimpleGraph.adj_comm] using h)
    have hk1 : seidel_matrix G u k
        = seidel_matrix_compl_codegree_eq_g G u k - (if k = u then 1 else 0) := by
      rw [seidel_matrix_compl_codegree_eq_entry]
      by_cases h : k = u
      · simp [h]
      · simp [h, Ne.symm h]
    have hk2 : seidel_matrix G k v
        = seidel_matrix_compl_codegree_eq_g G v k - (if k = v then 1 else 0) := by
      rw [seidel_matrix_compl_codegree_eq_entry, seidel_matrix_compl_codegree_eq_g_symm]
    rw [hk1, hk2]
    by_cases h1 : k = u
    · rw [h1]
      simp [seidel_matrix_compl_codegree_eq_g, hne, hna', SimpleGraph.irrefl]
    · by_cases h2 : k = v
      · rw [h2]
        simp [seidel_matrix_compl_codegree_eq_g, Ne.symm hne, hna, SimpleGraph.irrefl]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

private lemma seidel_matrix_compl_codegree_eq_key_pointwise {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v k : V) :
    seidel_matrix_compl_codegree_eq_g G u k + seidel_matrix_compl_codegree_eq_g G v k
        + seidel_matrix_compl_codegree_eq_g G u k * seidel_matrix_compl_codegree_eq_g G v k
      = 4 * (if (¬ G.Adj u k ∧ ¬ G.Adj v k) then (1:ℤ) else 0) - 1 := by
  unfold seidel_matrix_compl_codegree_eq_g
  by_cases h1 : G.Adj u k <;> by_cases h2 : G.Adj v k <;> simp [h1, h2]

private lemma seidel_matrix_compl_codegree_eq_key_sum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) :
    (∑ k : V, (seidel_matrix_compl_codegree_eq_g G u k + seidel_matrix_compl_codegree_eq_g G v k
        + seidel_matrix_compl_codegree_eq_g G u k * seidel_matrix_compl_codegree_eq_g G v k))
      = 4 * ((Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k)).card : ℤ)
        - (Fintype.card V : ℤ) := by
  have h : ∀ k : V, seidel_matrix_compl_codegree_eq_g G u k + seidel_matrix_compl_codegree_eq_g G v k
        + seidel_matrix_compl_codegree_eq_g G u k * seidel_matrix_compl_codegree_eq_g G v k
      = 4 * (if (¬ G.Adj u k ∧ ¬ G.Adj v k) then (1:ℤ) else 0) - 1 :=
    fun k => seidel_matrix_compl_codegree_eq_key_pointwise G u v k
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp

private lemma seidel_matrix_compl_codegree_eq_compl_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : Gᶜ.Adj u v) :
    (Fintype.card (Gᶜ.commonNeighbors u v) : ℤ)
      = ((Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k)).card : ℤ) - 2 := by
  obtain ⟨hne, hna⟩ := (SimpleGraph.compl_adj G u v).mp huv
  have hna' : ¬ G.Adj v u := fun h => hna (by simpa [SimpleGraph.adj_comm] using h)
  have hset : (Gᶜ.commonNeighbors u v).toFinset
      = Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k) \ {u, v} := by
    ext w
    simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, SimpleGraph.compl_adj,
      Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  have hsub : ({u, v} : Finset V) ⊆
      Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact ⟨SimpleGraph.irrefl G, hna'⟩
    · exact ⟨hna, SimpleGraph.irrefl G⟩
  have h1 : (Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k) \ {u, v}).card
      + ({u, v} : Finset V).card
      = (Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k)).card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have h2 : ({u, v} : Finset V).card = 2 := Finset.card_pair hne
  have h3 : (Fintype.card (Gᶜ.commonNeighbors u v) : ℤ)
      = ((Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k) \ {u, v}).card : ℤ) := by
    rw [← Set.toFinset_card (Gᶜ.commonNeighbors u v), hset]
  rw [h2] at h1
  have h4 : ((Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k) \ {u, v}).card : ℤ) + 2
      = ((Finset.univ.filter (fun k : V => ¬ G.Adj u k ∧ ¬ G.Adj v k)).card : ℤ) := by
    exact_mod_cast h1
  linarith

/-- Codegree formula in the complement graph in terms of the Seidel matrix. -/
theorem seidel_matrix_compl_codegree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : Gᶜ.Adj u v) :
    4 * (Fintype.card (Gᶜ.commonNeighbors u v) : ℤ) =
      (Fintype.card V : ℤ) - 4 + (∑ k : V, seidel_matrix G u k) + (∑ k : V, seidel_matrix G v k) +
        (seidel_matrix G * seidel_matrix G) u v := by
  obtain ⟨hne, hna⟩ := (SimpleGraph.compl_adj G u v).mp huv
  have hru := seidel_matrix_compl_codegree_eq_row_sum G u
  have hrv := seidel_matrix_compl_codegree_eq_row_sum G v
  have hsq := seidel_matrix_compl_codegree_eq_sq_entry G hne hna
  have hkey := seidel_matrix_compl_codegree_eq_key_sum G u v
  have hcard := seidel_matrix_compl_codegree_eq_compl_card G huv
  have hsplit : (∑ k : V, (seidel_matrix_compl_codegree_eq_g G u k
        + seidel_matrix_compl_codegree_eq_g G v k
        + seidel_matrix_compl_codegree_eq_g G u k * seidel_matrix_compl_codegree_eq_g G v k))
      = (∑ k : V, seidel_matrix_compl_codegree_eq_g G u k)
        + (∑ k : V, seidel_matrix_compl_codegree_eq_g G v k)
        + (∑ k : V, seidel_matrix_compl_codegree_eq_g G u k * seidel_matrix_compl_codegree_eq_g G v k) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith
