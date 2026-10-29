import AFTD.Prelude
import AFTD.Kb.Tcs.IsAmplyRegular

/-!
# amply_regular_sphere_two_card_mul

Topic: graphs   Node: fe3e2ace3afb

Provenance: helper lemma. step towards amply_regular_diameter_bound_conjecture

In an amply regular graph with parameters (k, ℓ, μ), for every vertex v the number of vertices at distance exactly 2 from v, multiplied by μ, equals k(k − 1 − ℓ).
-/

/-- The sphere-size identity for amply regular graphs: k(k−1−ℓ) = |S₂(v)|·μ, so the second neighbourhood has size k(k−1−ℓ)/μ. -/
theorem amply_regular_sphere_two_card_mul {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k ℓ μ : ℕ} (hG : IsAmplyRegular G k ℓ μ) (v : V) :
    (Finset.univ.filter (fun w => G.dist v w = 2)).card * μ = k * (k - 1 - ℓ) := by
  classical
  open SimpleGraph in
  have sum_z_d_add (w : V) (hvw : G.Adj v w) :
      (∑ z : V, if G.Adj w z ∧ G.dist v z = 2 then (1:ℕ) else 0) + 1 + ℓ = k := by
    have hid (z : V) :
      (if G.Adj w z ∧ G.dist v z = 2 then 1 else 0) +
      (if G.Adj w z ∧ z = v then 1 else 0) +
      (if G.Adj w z ∧ G.Adj v z then 1 else 0) =
      (if G.Adj w z then (1 : ℕ) else 0) := by
      by_cases hwz : G.Adj w z
      · simp only [hwz, true_and, ite_true]
        by_cases hzv : z = v
        · have hnotadj : ¬ G.Adj v z := by rw [hzv]; exact G.irrefl
          have hdist : G.dist v z ≠ 2 := by rw [hzv, SimpleGraph.dist_self]; decide
          simp only [if_pos hzv, if_neg hnotadj, if_neg hdist, add_zero, zero_add]
        · simp only [if_neg hzv, add_zero]
          by_cases hvz : G.Adj v z
          · have hd1 : G.dist v z = 1 := dist_eq_one_iff_adj.mpr hvz
            have hd2 : G.dist v z ≠ 2 := by rw [hd1]; decide
            simp only [if_pos hvz, if_neg hd2, zero_add]
          · have hd2 : G.dist v z = 2 := by
              let p : G.Walk v z := Walk.cons hvw (Walk.cons hwz Walk.nil)
              have hp : p.length = 2 := by simp [p]
              have hle : G.dist v z ≤ 2 := hp ▸ G.dist_le p
              have hr : G.Reachable v z := ⟨p⟩
              have hne0 : G.dist v z ≠ 0 := fun h0 => hzv (hr.dist_eq_zero_iff.mp h0).symm
              have hne1 : G.dist v z ≠ 1 := fun h1 => hvz (dist_eq_one_iff_adj.mp h1)
              omega
            simp only [if_neg hvz, if_pos hd2, add_zero]
      · simp [hwz]
    have hsum : ∑ z : V, ((if G.Adj w z ∧ G.dist v z = 2 then 1 else 0) +
                          (if G.Adj w z ∧ z = v then 1 else 0) +
                          (if G.Adj w z ∧ G.Adj v z then 1 else 0)) =
                ∑ z : V, if G.Adj w z then (1:ℕ) else 0 :=
      Finset.sum_congr rfl (fun z _ => hid z)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have ha : (∑ z : V, if G.Adj w z ∧ z = v then 1 else 0) = 1 := by
      have : (∑ z : V, if G.Adj w z ∧ z = v then 1 else 0) =
             ∑ z : V, (if z = v then (if G.Adj w z then (1:ℕ) else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = v <;> simp [hx]
      rw [this]
      simp [hvw.symm]
    have hc : (∑ z : V, if G.Adj w z ∧ G.Adj v z then (1:ℕ) else 0) = ℓ := by
      have : (∑ z : V, if G.Adj w z ∧ G.Adj v z then (1:ℕ) else 0) =
             (Finset.univ.filter (fun z => G.Adj w z ∧ G.Adj v z)).card := by
        rw [← Finset.sum_filter]
        simp
      have hcomm : (Finset.univ.filter (fun z => G.Adj w z ∧ G.Adj v z)) =
                   (G.commonNeighbors w v).toFinset := by
        ext x
        simp [mem_commonNeighbors]
      rw [this, hcomm, Set.toFinset_card, hG.adj_commonNeighbors hvw.symm]
    have ht : (∑ z : V, if G.Adj w z then (1:ℕ) else 0) = k := by
      have : (∑ z : V, if G.Adj w z then (1:ℕ) else 0) = (G.neighborFinset w).card := by
        rw [← Finset.sum_filter]
        have hfilt : (Finset.univ.filter (fun z => G.Adj w z)) = G.neighborFinset w := by
          ext x
          simp [neighborFinset, mem_neighborSet]
        rw [hfilt]
        exact (Finset.card_eq_sum_ones (G.neighborFinset w)).symm
      rw [this, card_neighborFinset_eq_degree, hG.regular w]
    rw [ha, hc] at hsum
    rw [ht] at hsum
    exact hsum

  have way1 : (∑ w : V, ∑ z : V, (if G.Adj v w ∧ G.Adj w z ∧ G.dist v z = 2 then (1:ℕ) else 0)) =
      k * (k - 1 - ℓ) := by
    have hw (w : V) : (∑ z : V, if G.Adj v w ∧ G.Adj w z ∧ G.dist v z = 2 then (1:ℕ) else 0) =
                       if G.Adj v w then k - 1 - ℓ else 0 := by
      by_cases hvw : G.Adj v w
      · simp only [hvw, true_and, if_pos]
        have h := sum_z_d_add w hvw
        omega
      · simp only [hvw, false_and, if_neg, not_false_eq_true]
        exact Finset.sum_const_zero
    simp_rw [hw]
    have hmul : (∑ w : V, if G.Adj v w then k - 1 - ℓ else 0) =
                (k - 1 - ℓ) * (∑ w : V, if G.Adj v w then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : G.Adj v x <;> simp [h]
    rw [hmul]
    have ht : (∑ w : V, if G.Adj v w then (1:ℕ) else 0) = k := by
      have : (∑ w : V, if G.Adj v w then (1:ℕ) else 0) = (G.neighborFinset v).card := by
        rw [← Finset.sum_filter]
        have hfilt : (Finset.univ.filter (fun w => G.Adj v w)) = G.neighborFinset v := by
          ext x
          simp [neighborFinset, mem_neighborSet]
        rw [hfilt]
        exact (Finset.card_eq_sum_ones (G.neighborFinset v)).symm
      rw [this, card_neighborFinset_eq_degree, hG.regular v]
    rw [ht, mul_comm]

  have way2 : (∑ z : V, ∑ w : V, (if G.Adj v w ∧ G.Adj w z ∧ G.dist v z = 2 then (1:ℕ) else 0)) =
      (Finset.univ.filter (fun w => G.dist v w = 2)).card * μ := by
    have hz (z : V) : (∑ w : V, if G.Adj v w ∧ G.Adj w z ∧ G.dist v z = 2 then (1:ℕ) else 0) =
                       if G.dist v z = 2 then μ else 0 := by
      by_cases hdist : G.dist v z = 2
      · simp only [hdist, and_true, if_pos]
        have heq : (∑ w : V, if G.Adj v w ∧ G.Adj w z then (1:ℕ) else 0) =
                   (Finset.univ.filter (fun w => G.Adj v w ∧ G.Adj w z)).card := by
          rw [← Finset.sum_filter]
          simp
        have hfilt : (Finset.univ.filter (fun w => G.Adj v w ∧ G.Adj w z)) =
                     (G.commonNeighbors v z).toFinset := by
          ext x
          simp [SimpleGraph.mem_commonNeighbors, SimpleGraph.adj_comm]
        rw [heq, hfilt, Set.toFinset_card, hG.dist_two_commonNeighbors hdist]
      · simp only [hdist, and_false, if_neg, not_false_eq_true]
        exact Finset.sum_const_zero
    simp_rw [hz]
    have hmul : (∑ z : V, if G.dist v z = 2 then μ else 0) =
                μ * (∑ z : V, if G.dist v z = 2 then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : G.dist v x = 2 <;> simp [h]
    rw [hmul]
    have hcard : (∑ z : V, if G.dist v z = 2 then (1:ℕ) else 0) =
                 (Finset.univ.filter (fun w => G.dist v w = 2)).card := by
      rw [← Finset.sum_filter]
      simp
    rw [hcard, mul_comm]

  rw [← way2, Finset.sum_comm, way1]
