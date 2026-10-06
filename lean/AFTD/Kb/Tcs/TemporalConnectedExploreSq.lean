import AFTD.Prelude
import AFTD.Kb.Tcs.IsTemporalWalk
import AFTD.Kb.Tcs.TemporalWalkExploresBy

/-!
# temporal_connected_explore_sq

Topic: graphs   Node: 695a4d8ba7a4

Provenance: formalization of a published result. Source: On Temporal Graph Exploration (ICALP 2015), the O(n²) upper bound for always-connected temporal graphs, recalled as [24] in arXiv:2610.06228, Sec. 1; the Lean states the explicit bound (n − 1)² from the standard reachability argument

Every temporal graph on n vertices all of whose snapshots are connected can be explored from any start vertex within (n − 1)² time steps.
-/

theorem temporal_connected_reach_within {n : ℕ} (G : ℕ → SimpleGraph (Fin n))
    (hG : ∀ t, (G t).Connected) (t0 : ℕ) (v u : Fin n) :
    ∃ w : ℕ → Fin n, w 0 = v ∧ (∀ i, w (i + 1) = w i ∨ (G (t0 + i)).Adj (w i) (w (i + 1))) ∧
      ∃ j ≤ n - 1, w j = u := by
  classical
  let R : ℕ → Finset (Fin n) := fun j => Finset.univ.filter fun y =>
    ∃ p : ℕ → Fin n, p 0 = v ∧ (∀ i < j, p (i + 1) = p i ∨ (G (t0 + i)).Adj (p i) (p (i + 1))) ∧
      p j = y
  have hmono : ∀ j, R j ⊆ R (j + 1) := by
    intro j y hy
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨p, hp0, hp, hpj⟩ := hy
    refine ⟨fun i => if i ≤ j then p i else y, by simp [hp0], fun i hi => ?_, by simp⟩
    rcases Nat.lt_or_ge i j with h | h
    · have := hp i h
      simp only [show i ≤ j from h.le, show i + 1 ≤ j from h, if_true]
      exact this
    · obtain rfl : i = j := by omega
      left; simp [hpj]
  have hv : v ∈ R 0 := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => v, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  have hgrow : ∀ j, R j ≠ Finset.univ → (R j).card < (R (j + 1)).card := by
    intro j hj
    obtain ⟨z, hz⟩ : ∃ z, z ∉ R j := by
      by_contra h; push Not at h; exact hj (Finset.eq_univ_iff_forall.2 h)
    have hvj : v ∈ R j := by
      clear hz hj
      induction j with
      | zero => exact hv
      | succ j ih => exact hmono j ih
    obtain ⟨wk⟩ := (hG (t0 + j)).preconnected v z
    obtain ⟨d, -, hd1, hd2⟩ := wk.exists_boundary_dart (↑(R j) : Set (Fin n)) hvj hz
    refine Finset.card_lt_card ((hmono j).ssubset_of_not_subset fun hsub => hd2 ?_)
    have hy : d.snd ∈ R (j + 1) := by
      have h1 : d.fst ∈ R j := hd1
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
      obtain ⟨p, hp0, hp, hpj⟩ := h1
      refine ⟨fun i => if i ≤ j then p i else d.snd, by simp [hp0], fun i hi => ?_, by simp⟩
      rcases Nat.lt_or_ge i j with h | h
      · simp only [show i ≤ j from h.le, show i + 1 ≤ j from h, if_true]
        exact hp i h
      · obtain rfl : i = j := by omega
        right; simpa [hpj] using d.adj
    exact hsub hy
  have hcard : ∀ j, min (j + 1) n ≤ (R j).card := by
    intro j
    induction j with
    | zero =>
      have := Finset.card_pos.2 ⟨v, hv⟩
      omega
    | succ j ih =>
      by_cases hj : R j = Finset.univ
      · have : R (j + 1) = Finset.univ := Finset.eq_univ_of_forall fun y =>
          hmono j (by rw [hj]; exact Finset.mem_univ y)
        rw [this, Finset.card_univ, Fintype.card_fin]; omega
      · have := hgrow j hj; omega
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact v.elim0
  have hfull : R (n - 1) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := hcard (n - 1)
    have hle := Finset.card_le_univ (R (n - 1))
    simp only [Fintype.card_fin] at hle ⊢
    omega
  have hu : u ∈ R (n - 1) := by rw [hfull]; exact Finset.mem_univ u
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨p, hp0, hp, hpj⟩ := hu
  refine ⟨fun i => if i ≤ n - 1 then p i else u, by simp [hp0], fun i => ?_,
    ⟨n - 1, le_rfl, by simp [hpj]⟩⟩
  rcases Nat.lt_or_ge i (n - 1) with h | h
  · simp only [show i ≤ n - 1 from h.le, show i + 1 ≤ n - 1 from h, if_true]
    exact hp i h
  · left
    have h1 : ¬ (i + 1 ≤ n - 1) := by omega
    simp only [h1, if_false]
    by_cases h2 : i ≤ n - 1
    · obtain rfl : i = n - 1 := by omega
      simp [hpj]
    · simp [h2]

theorem temporal_connected_visit_list {n : ℕ} (G : ℕ → SimpleGraph (Fin n))
    (hG : ∀ t, (G t).Connected) (L : List (Fin n)) :
    ∀ (t0 : ℕ) (v : Fin n), ∃ w : ℕ → Fin n, w 0 = v ∧
      (∀ i, w (i + 1) = w i ∨ (G (t0 + i)).Adj (w i) (w (i + 1))) ∧
      ∀ u ∈ L, ∃ j ≤ L.length * (n - 1), w j = u := by
  induction L with
  | nil =>
    intro t0 v
    exact ⟨fun _ => v, rfl, fun _ => Or.inl rfl, fun u hu => absurd hu List.not_mem_nil⟩
  | cons a L ih =>
    intro t0 v
    obtain ⟨q, hq0, hq, j, hj, hqj⟩ := temporal_connected_reach_within G hG t0 v a
    obtain ⟨p, hp0, hp, hpL⟩ := ih (t0 + j) a
    refine ⟨fun i => if i ≤ j then q i else p (i - j), by simp [hq0], fun i => ?_, ?_⟩
    · rcases Nat.lt_or_ge i j with h | h
      · simp only [show i ≤ j from h.le, show i + 1 ≤ j from h, if_true]
        exact hq i
      · have h1 : ¬ (i + 1 ≤ j) := by omega
        simp only [h1, if_false]
        have hpi := hp (i - j)
        have e1 : i - j + 1 = i + 1 - j := by omega
        have e2 : t0 + j + (i - j) = t0 + i := by omega
        rw [e1, e2] at hpi
        by_cases h2 : i ≤ j
        · obtain rfl : i = j := by omega
          simp only [le_refl, if_true, hqj]
          simpa [hp0] using hpi
        · simp only [h2, if_false]
          exact hpi
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · refine ⟨j, ?_, by simp [hqj]⟩
        rw [List.length_cons]
        exact le_trans hj (Nat.le_mul_of_pos_left (n - 1) (Nat.succ_pos _))
      · obtain ⟨k, hk, hpk⟩ := hpL u hu
        refine ⟨j + k, by rw [List.length_cons, add_mul, one_mul]; omega, ?_⟩
        by_cases hk0 : k = 0
        · subst hk0
          simp only [Nat.add_zero, le_refl, if_true]
          rw [hqj, ← hpk, hp0]
        · have : ¬ (j + k ≤ j) := by omega
          simp only [this, if_false, Nat.add_sub_cancel_left, hpk]

theorem temporal_connected_explore_sq :
    ∀ (n : ℕ) (G : ℕ → SimpleGraph (Fin n)), (∀ t, (G t).Connected) →
      ∀ s : Fin n, ∃ w : ℕ → Fin n, w 0 = s ∧ is_temporal_walk G w ∧
        temporal_walk_explores_by w ((n - 1) ^ 2) := by
  classical
  intro n G hG s
  obtain ⟨w, hw0, hw, hL⟩ := temporal_connected_visit_list G hG (Finset.univ.erase s).toList 0 s
  refine ⟨w, hw0, fun t => by simpa using hw t, fun u => ?_⟩
  by_cases hu : u = s
  · exact ⟨0, Nat.zero_le _, hu ▸ hw0⟩
  · obtain ⟨j, hj, hwj⟩ := hL u (by simp [hu])
    refine ⟨j, le_trans hj ?_, hwj⟩
    simp only [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ s),
      Finset.card_univ, Fintype.card_fin]
    rw [sq]
